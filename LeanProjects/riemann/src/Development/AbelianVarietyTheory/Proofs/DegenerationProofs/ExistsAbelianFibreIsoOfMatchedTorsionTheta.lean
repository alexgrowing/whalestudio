import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

namespace GlobalTheory.Ex.FibIso

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

def Reads {F : Type} [Field F] (B : NumB F) (Q : PolAV (Sp F)) (E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ b b' : B.A, b ^ k = 1 → b' ^ k = 1 →
    WeilIs Q.A Q.L k (E b) (E b') (unitOn (B.weil k b b'))) ∧
  ∀ m : ℕ, Odd m → (m : F) ≠ 0 → ∀ (Ix : Type) (b : Ix → B.A), (∀ i, b i ^ m ^ 2 = 1) →
    IsThetaPt Q m (fun i => E (b i)) (fun i => fnOf (B.uth m (b i) 1))

theorem exists_reads (hU : BrUthSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (h₁ : D.PsiEven)
    (h₂ : D.TauBimult) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F}
    (ν : NumOf D F N) {Q : PolAV (Sp F)} {Φ : Q.A.left ⟶ D.P.A.left} (hΦ : IsFib D F Q Φ) :
    ∃ E : N.A ≃* (baseOver (Sp F) ⟶ Q.A), (∀ b, (ν.eA b).left = (E b).left ≫ Φ) ∧ Reads N.toNumB Q E := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hΦ.1 (𝟙 (Sp F)) (TF (R := R) F).hom (Category.id_comp _).symm
  obtain ⟨w, t⟩ := hU R D h₁ h₂ F N ν
  have hE : ∀ b, (ν.eA b).left = ((ν.eA.trans e.symm) b).left ≫ Φ := fun b =>
    (congrArg (fun z => z.left) (e.apply_symm_apply (ν.eA b)).symm).trans (he _)
  refine ⟨ν.eA.trans e.symm, hE, fun k hk b b' hb hb' => ?_, fun m hm hm' Ix b hb => ?_⟩
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x y : baseOver (Sp F) ⟶ Q.A)
        (x₀ y₀ : Over.mk s ⟶ D.P.A) (c : Γ(Sp F, ⊤)ˣ), x₀.left = x.left ≫ Φ → y₀.left = y.left ≫ Φ →
        WeilIs D.P.A D.P.L k x₀ y₀ c → WeilIs Q.A Q.L k x y c := by
      rintro s rfl x y x₀ y₀ c hx hy h
      have := Q.isAb.comm
      exact (weilIs_grpPullback_of_comm' _ _ _ _ _ Φ _ _ D.P.isLB Q.isLB hΦ.1 hΦ.2.1 (baseOver _) k x y x₀ y₀ c
        hx hy).2 h
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hE b) (hE b') (w k hk b b' hb hb')
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x : Ix → (baseOver (Sp F) ⟶ Q.A))
        (x₀ : Ix → (Over.mk s ⟶ D.P.A)) (v : Ix → Γ(Sp F, ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ Φ) →
        (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt D.P m x₀ v → IsThetaPt Q m x v := by
      rintro s rfl x x₀ v hx hp h
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp F)) hΦ.1 hΦ.2.1 hx hp _).2 h
    exact key _ (Category.id_comp _).symm _ _ _ (fun i => hE (b i))
      (fun i => by rw [← map_pow, hb, map_one]) (t m hm hm' Ix b hb).1

theorem linComb_map {S : Scheme.{0}} {A T : Over S} [GrpObj A] {G : Type} [Group G] (f : G →* (T ⟶ A)) {r : ℕ}
    (y : Fin r → G) (a : Fin r → ℕ) :
    linComb (fun i => f (y i)) a = f (List.ofFn fun i => y i ^ a i).prod := by
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (map_pow f (y i) (a i)).symm))

theorem exists_level (hL : Laws) {F : Type} [Field F] (Q : PolAV (Sp F)) {g : ℕ} (hg : Q.g = g) {M : ℕ}
    (hM : (M : F) ≠ 0) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M) (x : Fin (2 * g) → (baseOver (Sp F) ⟶ Q.A))
    (hx : ∀ i, x i ^ M = 1) (hp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζ ^ stdSymp g i j)) :
    ∃ lev : Out.Level Q M (unitOn ζ), levelBasis lev hg = x := by
  subst hg
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  refine exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ Q M _
    (hζ.map_of_injective (Units.map_injective inj)) (fun K _ s => ⟨?_, ?_⟩) x hx hp
  · rw [← map_natCast (Spec.preimage s).hom]
    exact (map_ne_zero _).2 hM
  · have : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.nontrivial
    exact hζ.map_of_injective (Units.map_injective
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).injective)

theorem exists_iso_of_reads (hL : Laws) (hT : ThetaPtDeterminesSt) {F : Type} [Field F] [IsAlgClosed F]
    {B B' : NumB F} {Q Q' : PolAV (Sp F)} (hg : Q'.g = Q.g) {E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)}
    {E' : B'.A ≃* (baseOver (Sp F) ⟶ Q'.A)} (hE : Reads B Q E) (hE' : Reads B' Q' E') {n : ℕ} (hn : n.Prime)
    (ho : Odd n) (hF : (n : F) ≠ 0) : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : B.A → B'.A), c ≠ 0 →
      TorsMap B B' (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧
        ∀ b, b ^ (n ^ j) ^ 2 = 1 → E b ≫ σ.hom = E' (ρ b) := by
  refine ⟨((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial + 4, fun J hJ c ρ hc hρ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : ((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial < n ^ (j + 4) :=
    lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hm : ((n ^ (j + 4) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hF
  have hM : (((n ^ (j + 4)) ^ 2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hm
  have hM1 : 1 ≤ (n ^ (j + 4)) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hlev := nonempty_level_prime_pow hL F Q n ((j + 4) * 2) hn hF
  rw [pow_mul] at hlev
  have hT' := hT Q.g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) hB F hF Q Q' rfl hg
  have hom : Odd (n ^ (j + 4)) := ho.pow
  generalize n ^ (j + 4) = m at *
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨hM⟩
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨lev⟩ := hlev (unitOn ζ) (hζ.map_of_injective (Units.map_injective inj))
  let T : Subgroup B.A := (powMonoidHom (m ^ 2)).ker
  let f : T →* (baseOver (Sp F) ⟶ Q.A) := E.toMonoidHom.comp T.subtype
  let f' : T →* (baseOver (Sp F) ⟶ Q'.A) :=
    E'.toMonoidHom.comp (MonoidHom.mk' (fun t => ρ t.1) fun s t => (hρ.1 s.1 t.1 s.2 t.2).1)
  let b : Fin (2 * Q.g) → T := fun i => ⟨E.symm (lev.pt i), by
    show E.symm (lev.pt i) ^ m ^ 2 = 1
    rw [← map_pow, lev.torsion, map_one]⟩
  have hb : lev.pt = fun i => f (b i) := funext fun i => (E.apply_symm_apply _).symm
  obtain ⟨lev', hb'⟩ := exists_level hL Q' hg hM hζ (fun i => f' (b i))
    (fun i => by
      show E' (ρ (b i).1) ^ m ^ 2 = 1
      rw [← map_pow, (hρ.2 _ (b i).2).1, map_one])
    (fun i k => by
      have p₁ := hE.1 _ hM1 _ _ (b i).2 (b k).2
      have p₂ := hE'.1 _ hM1 _ _ (hρ.2 _ (b i).2).1 (hρ.2 _ (b k).2).1
      rw [(hρ.1 _ _ (b i).2 (b k).2).2] at p₂
      simp only [b, MulEquiv.apply_symm_apply] at p₁
      rw [← ((hL.weil _ Q (m ^ 2) (baseOver _)).1 _ _ (lev.torsion i) (lev.torsion k)).unique p₁ (lev.pairing i k)]
      exact p₂)
  let t : (Fin (2 * Q.g) → ℕ) → T := fun a => (List.ofFn fun i => b i ^ a i).prod
  have e : ∀ a, linComb lev.pt a = E (t a).1 := fun a => by rw [hb]; exact linComb_map f b a
  have e' : ∀ a, linComb (levelBasis lev' hg) a = E' (ρ (t a).1) := fun a => by rw [hb']; exact linComb_map f' b a
  let u : (Fin (2 * Q.g) → ZMod (m ^ 2)) → B.A := fun a => (t fun i => (a i).val).1
  have hu : ∀ a, u a ^ m ^ 2 = 1 := fun a => (t _).2
  have v₁ := isThetaPt_mul (fnOf c) ((IsUnit.mk0 c hc).map _) (hE.2 m hom hm _ u hu)
  have v₂ := hE'.2 m hom hm _ (fun a => ρ (u a)) fun a => (hρ.2 _ (hu a)).1
  have q : (fun a => fnOf (B'.uth m (ρ (u a)) 1)) = fun a => fnOf c * fnOf (B.uth m (u a) 1) :=
    funext fun a => by rw [(hρ.2 _ (hu a)).2]; exact map_mul _ _ _
  rw [q] at v₂
  have l : levelPoint lev rfl = fun a => E (u a) := funext fun a => e _
  have l' : levelPoint lev' hg = fun a => E' (ρ (u a)) := funext fun a =>
    (ThetaPtDet.levelPoint_eq _ _ _).trans (e' _)
  obtain ⟨σ, hσ, hσb⟩ := hT' _ lev lev' _ (l ▸ v₁) (l' ▸ v₂)
  refine ⟨σ, hσ, fun x hx => ?_⟩
  have := hσ.1
  obtain ⟨d, hd⟩ := lev.span F (𝟙 _) (E x) (by rw [← map_pow, hx, map_one])
  have hd' : linComb lev.pt (fun i => (d i : ℕ)) = E x :=
    (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
  have hx' : x = (t fun i => (d i : ℕ)).1 := E.injective (hd'.symm.trans (e _))
  rw [← hd', ThetaPtDet.linComb_comp, hx', ← e']
  exact congrArg (linComb · _) (funext hσb)

theorem exists_iso_fib : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  intro hL hT hU R _ _ D D' a₁ a₂ a₃ a₄ hg F _ _ _ N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hF
  obtain ⟨E, hE, rE⟩ := exists_reads hU a₁ a₂ ν hΦ
  obtain ⟨E', hE', rE'⟩ := exists_reads hU a₃ a₄ ν' hΦ'
  obtain ⟨j₀, h⟩ := exists_iso_of_reads hL hT (hΦ'.2.2.trans (hg.symm.trans hΦ.2.2.symm)) rE rE' hn ho hF
  refine ⟨j₀, fun j hj c ρ hc hρ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := h j hj c ρ hc hρ
  refine ⟨σ, hσ, fun x b hb' hx => ?_⟩
  obtain rfl : x = E b := Over.OverMorphism.ext
    (hΦ.1.1.hom_ext (hx.symm.trans (hE b)) (by rw [Over.w, Over.w]))
  rw [hb b hb', hE']

end GlobalTheory.Ex.FibIso
