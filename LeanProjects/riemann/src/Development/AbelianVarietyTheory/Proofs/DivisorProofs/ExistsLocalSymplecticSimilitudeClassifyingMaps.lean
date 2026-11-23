import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSimilitudeOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_sympLev_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'}
    {f : S' ⟶ S} (m : ObjMap o' o f) {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {t₁ : S ⟶ Sp B}
    {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    ∃ l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ o'.A), IsSympLev o'.P h M ζ (f ≫ t₁) l ∧
      ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left := by
  refine ⟨fun a => GlobalTheory.ObjPull.secPull m.cart (lev a), ⟨fun a c => by dsimp only; rw [hl.1, map_mul],
    fun a => by dsimp only; rw [← map_pow, hl.2.1, map_one], fun k _ _ x β z hx hz => ?_⟩,
    fun a => GlobalTheory.ObjPull.secPull_left m.cart _⟩
  let Φ := GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)
  have hΦ : ∀ a, Φ (toUnit _ ≫ GlobalTheory.ObjPull.secPull m.cart (lev a)) = toUnit (Over.mk (x ≫ f)) ≫ lev a :=
    fun a => GlobalTheory.ObjPull.pushEquiv_secPull m.cart _ _
  obtain ⟨hker, honto, hw⟩ := hl.2.2 k (x ≫ f) β z ((Category.assoc _ _ _).trans hx) hz
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← hker a, ← hΦ a]
    exact (map_eq_one_iff Φ Φ.injective).symm
  · obtain ⟨a, ha⟩ := honto (Φ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, Φ.injective ((hΦ a).trans ha)⟩
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.cart
      (DiagComp.diag_lbIso m) (Over.mk x) _ _ _ (toUnit (Over.mk (x ≫ f)) ≫ lev a)
      (toUnit (Over.mk (x ≫ f)) ≫ lev b) _ (by rw [← hΦ a]; rfl) (by rw [← hΦ b]; rfl)).2 (hw a b)

theorem reduceMod_eq_zero_iff {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) : reduceMod M a = 0 ↔ ∃ c, a = M • c := by
  constructor
  · intro ha
    have hd : ∀ i, (M : ℤ) ∣ a i := fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (congrFun ha i)
    choose c hc using hd
    exact ⟨c, funext fun i => by rw [Pi.smul_apply, hc i, nsmul_eq_mul]⟩
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaMod_reduceMod {h : ℕ} (M : ℕ) (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem lev_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] {h : ℕ} (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A))
    (hadd : ∀ a c, l (a + c) = l a * l c) (n : ℕ) (a : Fin h ⊕ Fin h → ℤ) : l (n • a) = l a ^ n := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {h : ℕ}

theorem ev_add (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (hl : ∀ a c, l (a + c) = l a * l c) {k : Type} [Field k]
    (y : Sp k ⟶ S) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l (a + c) = (toUnit (Over.mk y) ≫ l a) * (toUnit (Over.mk y) ≫ l c) := by
  rw [hl, MonObj.comp_mul]

theorem ev_sub (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (hl : ∀ a c, l (a + c) = l a * l c) {k : Type} [Field k]
    (y : Sp k ⟶ S) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l (a - c) = (toUnit (Over.mk y) ≫ l a) * (toUnit (Over.mk y) ≫ l c)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← ev_add l hl y, sub_add_cancel]

theorem ev_eq_iff {P : LB (G2 A).left} {M : ℕ} {B : Type} [CommRing B] {ζ : B} {t₁ : S ⟶ Sp B}
    {l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)} (hl : IsSympLev P h M ζ t₁ l) (k : Type) [Field k] [IsAlgClosed k]
    (y : Sp k ⟶ S) (β : B →+* k) (z : kˣ) (hy : y ≫ t₁ = spMap β) (hz : (z : k) = β ζ) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l a = toUnit (Over.mk y) ≫ l c ↔ reduceMod M a = reduceMod M c := by
  have hk := (hl.2.2 k y β z hy hz).1 (a - c)
  rw [ev_sub l hl.1 y, mul_inv_eq_one] at hk
  rw [hk, ← sub_eq_zero, ← reduceMod_eq_zero_iff]
  constructor <;> intro e
  · rw [← e]; funext i; simp [reduceMod]
  · rw [← e]; funext i; simp [reduceMod]

end

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_sim_point {h M : ℕ} (hM : 0 < M) (hodd : Odd M) {T : Scheme.{0}} {t : T ⟶ Sp R} (o : Obj b N t)
    {t₁ t₁' : T ⟶ Sp (cycAway M)} {l l' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)}
    (hl : IsSympLev o.P h M (zetaAway M) t₁ l) (hl' : IsSympLev o.P h M (zetaAway M) t₁' l')
    (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ T) (β β' : cycAway M →+* k) (hβ : y ≫ t₁ = spMap β)
    (hβ' : y ≫ t₁' = spMap β') :
    ∃ (a : sympSimGrp h M) (i : ℕ), (∀ u v, omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) u)
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) v) = (i : ZMod M) * omegaMod M u v) ∧
      β' (zetaAway M) = β (zetaAway M) ^ i ∧
      ∀ c, toUnit (Over.mk y) ≫ l' c = toUnit (Over.mk y) ≫ sympTwist a l c := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hzk : IsPrimitiveRoot (β (zetaAway M)) M := isPrimitiveRoot_map hM.ne' β
  have hzk' : IsPrimitiveRoot (β' (zetaAway M)) M := isPrimitiveRoot_map hM.ne' β'
  let z : kˣ := Units.mk0 _ (hzk.ne_zero hM.ne')
  let z' : kˣ := Units.mk0 _ (hzk'.ne_zero hM.ne')
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 hzk
  obtain ⟨-, onto, hw⟩ := hl.2.2 k y β z hβ rfl
  obtain ⟨-, -, hw'⟩ := hl'.2.2 k y β' z' hβ' rfl
  have E := ev_eq_iff hl k y β z hβ rfl
  have E' := ev_eq_iff hl' k y β' z' hβ' rfl
  have hpre : ∀ c : Fin h ⊕ Fin h → ℤ, ∃ B, toUnit (Over.mk y) ≫ l B = toUnit (Over.mk y) ≫ l' c := fun c =>
    onto _ (by rw [← MonObj.comp_pow, hl'.2.1, MonObj.comp_one])
  choose B hB using hpre
  let γ0 : (Fin h ⊕ Fin h → ZMod M) → (Fin h ⊕ Fin h → ZMod M) := fun c => reduceMod M (B (liftMod c))
  have hchar : ∀ c b, reduceMod M b = γ0 c ↔
      toUnit (Over.mk y) ≫ l b = toUnit (Over.mk y) ≫ l' (liftMod c) := fun c b => by
    rw [← hB, E]
  have hadd : ∀ c c', γ0 (c + c') = γ0 c + γ0 c' := fun c c' => by
    have e1 : reduceMod M (B (liftMod c) + B (liftMod c')) = reduceMod M (B (liftMod c)) + reduceMod M (B (liftMod c')) := by
      funext i; simp [reduceMod]
    show γ0 (c + c') = reduceMod M (B (liftMod c)) + reduceMod M (B (liftMod c'))
    rw [← e1]
    refine ((hchar _ _).2 ?_).symm
    rw [ev_add l hl.1 y, hB, hB, ← ev_add l' hl'.1 y, E']
    funext i; simp [reduceMod, liftMod]
  have hinj : Function.Injective γ0 := fun c c' e => by
    have h1 := (hchar c' (B (liftMod c))).1 e
    rw [hB, E', reduceMod_liftMod, reduceMod_liftMod] at h1
    exact h1
  let γl : (Fin h ⊕ Fin h → ZMod M) →ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M) :=
    (AddMonoidHom.mk' γ0 hadd).toZModLinearMap M
  have hγl : ∀ c, γl c = γ0 c := fun _ => rfl
  have hbij : Function.Bijective γl := by
    have hi : Function.Injective γl := fun c c' e => hinj (by rwa [hγl, hγl] at e)
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  let γe := LinearEquiv.ofBijective γl hbij
  have hγe : ∀ c, γe c = γ0 c := fun _ => rfl
  obtain ⟨i, -, hi⟩ := hzk.eq_pow_of_pow_eq_one hzk'.pow_eq_one
  have hi' : z ^ i = z' := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi)
  have hcop : i.Coprime M := (hz.pow_iff_coprime hM i).1 (hi' ▸ IsPrimitiveRoot.coe_units_iff.1 hzk')
  have h2 : IsUnit ((2 : ℕ) : ZMod M) := (ZMod.unitOfCoprime 2 (Nat.coprime_two_right.2 hodd).symm).isUnit
  have hpair : ∀ a c, ((omegaStd (B a) (B c) : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a c : ℤ) : ZMod M) := by
    intro a c
    have h1 := hw (B a) (B c)
    rw [hB, hB] at h1
    have e2 := GlobalTheory.weilIs_unique_fieldPoint T o.A _ (pull_isLB o.isLB _) k y M _ _ _ _ h1 (hw' a c)
    rw [← hi', ← zpow_natCast, ← zpow_mul] at e2
    have h3 : z ^ (2 * omegaStd (B a) (B c) - (i : ℤ) * (2 * omegaStd a c)) = 1 := by
      rw [zpow_sub, e2, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd] at h3
    have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 h3
    push_cast at h4
    have h5 : ((2 : ℕ) : ZMod M) * (((omegaStd (B a) (B c) : ℤ) : ZMod M) - (i : ZMod M) * ((omegaStd a c : ℤ) : ZMod M)) = 0 := by
      push_cast; linear_combination h4
    exact sub_eq_zero.1 (h2.mul_right_eq_zero.1 h5)
  have hsim : ∀ u v, omegaMod M (γe u) (γe v) = (i : ZMod M) * omegaMod M u v := by
    intro u v
    conv_rhs => rw [← reduceMod_liftMod u, ← reduceMod_liftMod v]
    rw [hγe, hγe, omegaMod_reduceMod, omegaMod_reduceMod, hpair]
  let m : (ZMod M)ˣ := ZMod.unitOfCoprime i hcop
  refine ⟨⟨γe, m, fun u v => by rw [hsim, ZMod.coe_unitOfCoprime]⟩, i, hsim, hi.symm, fun c => ?_⟩
  show _ = toUnit (Over.mk y) ≫ l (liftMod (γe (reduceMod M c)))
  rw [hγe, (hchar _ _).1 (reduceMod_liftMod _), E', reduceMod_liftMod]

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_spMap_eq {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem exists_open_eq_cycAway {M : ℕ} (hM : M ≠ 0) {T : Scheme.{0}} (f g : T ⟶ Sp (cycAway M)) (k : Type) [Field k]
    (y : Sp k ⟶ T) (hy : y ≫ f = y ≫ g) : ∃ V : T.Opens, Set.range y ⊆ (V : Set T) ∧ V.ι ≫ f = V.ι ≫ g := by
  haveI : FormallyUnramified (spMap (algebraMap ℤ (cycAway M))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact RingHom.formallyUnramified_algebraMap.2 (formallyUnramified_cycAway hM ℤ)
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ (cycAway M))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 (finiteType_cycAway M)
  have hab : f ≫ spMap (algebraMap ℤ (cycAway M)) = g ≫ spMap (algebraMap ℤ (cycAway M)) :=
    specZIsTerminal.hom_ext _ _
  haveI := GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified (spMap (algebraMap ℤ (cycAway M))) hab
  refine ⟨(equalizer.ι f g).opensRange, GlobalTheory.range_subset_range_equalizer_ι y hy, ?_⟩
  rw [← cancel_epi (equalizer.ι f g).isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
    Scheme.Hom.isoOpensRange_hom_ι, equalizer.condition]

theorem false_of_sympLev_zero {M : ℕ} (hM : 2 ≤ M) (hMp : M.Coprime p) {T : Scheme.{0}} {t : T ⟶ Sp R}
    (o : Obj b N t) {t₁ : T ⟶ Sp (cycAway M)} {l : (Fin 0 ⊕ Fin 0 → ℤ) → (𝟙_ (Over T) ⟶ o.A)}
    (hl : IsSympLev o.P 0 M (zetaAway M) t₁ l) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ T)
    (βR : R →+* k) (hR : y ≫ t = spMap βR) (β : cycAway M →+* k) (hβ : y ≫ t₁ = spMap β) : False := by
  have hM0 : 0 < M := by omega
  have hzk : IsPrimitiveRoot (β (zetaAway M)) M := isPrimitiveRoot_map hM0.ne' β
  obtain ⟨-, onto, -⟩ := hl.2.2 k y β (Units.mk0 _ (hzk.ne_zero hM0.ne')) hβ rfl
  obtain ⟨I, -⟩ := o.geom k y βR hR
  haveI := D.freeLa
  haveI := D.finLa
  let bs := Module.Free.chooseBasis ℤ D.La
  have hpos : 0 < Module.finrank ℤ D.La := by have := Datum.two_le_finrank_La D; omega
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ D.La) := by
    rw [← Fintype.card_pos_iff, ← Module.finrank_eq_card_chooseBasisIndex]; exact hpos
  have hnd : ¬ ∃ c, bs i₀ = M • c := by
    rintro ⟨c, hc⟩
    have e := congrArg (fun v => bs.repr v i₀) hc
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at e
    have : (M : ℤ) ∣ 1 := ⟨_, e⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  have hne : I.ev M (bs i₀) ≠ 1 := fun e => hnd ((I.ker M hM0 hMp _).1 e)
  have hpow : I.ev M (bs i₀) ^ M = 1 := (I.onto M hM0 hMp _).2 ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := onto _ hpow
  have ha0 : a = 0 := funext fun i => i.elim (fun j => j.elim0) (fun j => j.elim0)
  have l0 : l 0 = 1 := by
    have e := hl.1 0 0
    rw [add_zero] at e
    exact (mul_left_cancel (e.symm.trans (_root_.mul_one _).symm))
  rw [ha0, l0, MonObj.comp_one] at ha
  exact hne ha.symm

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

theorem exists_local_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : sympSimGrp h M), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  intro p _ D R _ b N h M hN hNp hM hodd hMp X s s₁ u lev hlev hU ρ hρ T t o x x' hx hx' ⟨m⟩ ⟨m'⟩ q
  obtain ⟨l, hl, hlp⟩ := exists_sympLev_pull m hlev
  obtain ⟨l', hl', hlp'⟩ := exists_sympLev_pull m' hlev
  let k := AlgebraicClosure (T.residueField q)
  let y : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField q) k)) ≫ T.fromSpecResidueField q
  have hyq : q ∈ Set.range y :=
    ⟨(⊥ : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply q _)⟩
  have hM0 : 0 < M := by omega
  haveI : NeZero M := ⟨hM0.ne'⟩
  obtain ⟨β, hβ⟩ := exists_spMap_eq (y ≫ x ≫ s₁)
  obtain ⟨β', hβ'⟩ := exists_spMap_eq (y ≫ x' ≫ s₁)
  obtain ⟨βR, hβR⟩ := exists_spMap_eq (y ≫ t)
  obtain ⟨a, i, hmul, hzi, ha⟩ := exists_sim_point hM0 hodd o hl hl' k y β β' hβ hβ'
  obtain ⟨hρs, ⟨n, σ, hn, hσ, hρ1⟩, ma, hma⟩ := hρ a
  have hz := isPrimitiveRoot_map hM0.ne' β
  have hni : β (zetaAway M) ^ n = β (zetaAway M) ^ i := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact (false_of_sympLev_zero (by omega) hMp o hl k y βR hβR β hβ).elim
    · let e₁ : Fin h ⊕ Fin h → ZMod M := Sum.elim (fun j => if j = ⟨0, hh⟩ then 1 else 0) (fun _ => 0)
      let e₂ : Fin h ⊕ Fin h → ZMod M := Sum.elim (fun _ => 0) (fun j => if j = ⟨0, hh⟩ then 1 else 0)
      have hω : omegaMod M e₁ e₂ = 1 := by simp [omegaMod, e₁, e₂]
      have h1 := (hn e₁ e₂).symm.trans (hmul e₁ e₂)
      rw [hω, _root_.mul_one, _root_.mul_one, ZMod.natCast_eq_natCast_iff'] at h1
      have key : ∀ j, β (zetaAway M) ^ j = β (zetaAway M) ^ (j % M) := fun j => by
        conv_lhs => rw [← Nat.mod_add_div j M, pow_add, pow_mul, hz.pow_eq_one, one_pow, _root_.mul_one]
      rw [key n, key i, h1]
  have hσβ : β.comp σ = β' := cycAway_hom_ext hM0.ne' (by rw [RingHom.comp_apply, hσ, map_pow, hni, hzi])
  have hy1 : y ≫ (x ≫ ρ a ≫ s₁) = y ≫ (x' ≫ s₁) := by
    calc y ≫ (x ≫ ρ a ≫ s₁) = (y ≫ x ≫ s₁) ≫ spMap σ := by rw [hρ1]; simp only [Category.assoc]
      _ = spMap (β.comp σ) := by rw [hβ, spMap, spMap, spMap, ← Spec.map_comp]; rfl
      _ = y ≫ x' ≫ s₁ := by rw [hσβ, hβ']
  obtain ⟨V₁, hV₁y, hV₁⟩ := exists_open_eq_cycAway hM0.ne' (x ≫ ρ a ≫ s₁) (x' ≫ s₁) k y hy1
  have hunit : IsUnit ((M : ℕ) : Γ(T, ⊤)) := by
    have h2 := ((b.unit M hMp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map t.appTop.hom
    simpa only [map_natCast] using h2
  have hV : ∀ c : Fin h ⊕ Fin h → ZMod M, ∃ W : T.Opens, Set.range y ⊆ (W : Set T) ∧
      W.ι ≫ (l' (liftMod c)).left = W.ι ≫ (sympTwist a l (liftMod c)).left := fun c =>
    GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point T o.A o.ab M hunit _ _ (hl'.2.1 _) (hl.2.1 _) k y (ha _)
  choose W hWy hW using hV
  let V : T.Opens := V₁ ⊓ ⟨⋂ c, (W c : Set T), isOpen_iInter_of_finite fun c => (W c).isOpen⟩
  have hqV : q ∈ V := ⟨hV₁y hyq, Set.mem_iInter.2 fun c => hWy c hyq⟩
  have hVW : ∀ c, V ≤ W c := fun c => fun z hz => Set.mem_iInter.1 hz.2 c
  have hV1 : V ≤ V₁ := fun z hz => hz.1
  have hagree : ∀ c, V.ι ≫ (l' c).left = V.ι ≫ (sympTwist a l c).left := by
    intro c
    have e1 : l' c = l' (liftMod (reduceMod M c)) := by
      obtain ⟨e, he⟩ := (reduceMod_eq_zero_iff (M := M) (c - liftMod (reduceMod M c))).1 (by
        funext j
        simp only [reduceMod, liftMod, Pi.zero_apply, Pi.sub_apply, Int.cast_sub, Int.cast_natCast,
          ZMod.natCast_zmod_val, sub_self])
      have hc : c = M • e + liftMod (reduceMod M c) := by rw [← he, sub_add_cancel]
      calc l' c = l' (M • e + liftMod (reduceMod M c)) := congrArg l' hc
        _ = l' (M • e) * l' (liftMod (reduceMod M c)) := hl'.1 _ _
        _ = _ := by rw [lev_nsmul l' hl'.1, hl'.2.1, _root_.one_mul]
    have e2 : sympTwist a l c = sympTwist a l (liftMod (reduceMod M c)) := by
      simp only [sympTwist, reduceMod_liftMod]
    rw [e1, e2, ← Scheme.homOfLE_ι T (hVW (reduceMod M c)), Category.assoc, Category.assoc, hW]
  have hVs : V.ι ≫ (x ≫ ρ a ≫ s₁) = V.ι ≫ (x' ≫ s₁) := by
    rw [← Scheme.homOfLE_ι T hV1, Category.assoc, Category.assoc, hV₁]
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N T V t V.ι o
  obtain ⟨lV, hlV, hlVp⟩ := exists_sympLev_pull mV hl'
  obtain ⟨f, -, huniq⟩ := hU V (V.ι ≫ t) (V.ι ≫ x' ≫ s₁) oV lV hlV
  have P1 : (V.ι ≫ x ≫ ρ a) ≫ s = V.ι ≫ t ∧ (V.ι ≫ x ≫ ρ a) ≫ s₁ = V.ι ≫ x' ≫ s₁ ∧
      ∃ m : ObjMap oV u (V.ι ≫ x ≫ ρ a), ∀ c, (lV c).left ≫ m.φ = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by simp only [Category.assoc, hρs, hx], by simpa only [Category.assoc] using hVs,
      mV.comp (m.comp ma), fun c => ?_⟩
    show (lV c).left ≫ (mV.φ ≫ (m.φ ≫ ma.φ)) = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left
    calc (lV c).left ≫ (mV.φ ≫ (m.φ ≫ ma.φ)) = ((lV c).left ≫ mV.φ) ≫ m.φ ≫ ma.φ := by
          simp only [Category.assoc]
      _ = (V.ι ≫ (l' c).left) ≫ m.φ ≫ ma.φ := by rw [hlVp c]
      _ = (V.ι ≫ (sympTwist a l c).left) ≫ m.φ ≫ ma.φ := by rw [hagree c]
      _ = V.ι ≫ ((sympTwist a l c).left ≫ m.φ) ≫ ma.φ := by simp only [Category.assoc]
      _ = V.ι ≫ (x ≫ (sympTwist a lev c).left) ≫ ma.φ := by
          rw [show (sympTwist a l c).left ≫ m.φ = x ≫ (sympTwist a lev c).left from hlp _]
      _ = V.ι ≫ x ≫ ((sympTwist a lev c).left ≫ ma.φ) := by simp only [Category.assoc]
      _ = V.ι ≫ x ≫ ρ a ≫ (lev c).left := by rw [hma c]
      _ = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left := by simp only [Category.assoc]
  have P2 : (V.ι ≫ x') ≫ s = V.ι ≫ t ∧ (V.ι ≫ x') ≫ s₁ = V.ι ≫ x' ≫ s₁ ∧
      ∃ m : ObjMap oV u (V.ι ≫ x'), ∀ c, (lV c).left ≫ m.φ = (V.ι ≫ x') ≫ (lev c).left := by
    refine ⟨by simp only [Category.assoc, hx'], Category.assoc _ _ _, mV.comp m', fun c => ?_⟩
    show (lV c).left ≫ (mV.φ ≫ m'.φ) = (V.ι ≫ x') ≫ (lev c).left
    rw [← Category.assoc, hlVp c, Category.assoc, hlp' c, Category.assoc]
  exact ⟨V, a, hqV, (huniq _ P1).trans (huniq _ P2).symm⟩

end GlobalTheory.HTLocSim
