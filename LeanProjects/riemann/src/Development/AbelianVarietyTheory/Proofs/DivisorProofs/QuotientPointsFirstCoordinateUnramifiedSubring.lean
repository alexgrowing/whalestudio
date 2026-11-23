import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemBasicOpenOfIsUnit
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DivPtsUnram

theorem exists_lift_finset {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] {T Ω F : Type} [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [Field Ω] [Field F] [IsAlgClosed F]
    (ρ : T →+* Ω) (hρ : IsLocalHom ρ) (j : T →+* F) (hj : Function.Injective j) {I : Type}
    (h : I → (Sp T ⟶ S)) (g : I → (Sp Ω ⟶ X)) (w : ∀ i, g i ≫ f = spMap ρ ≫ h i)
    (s : Finset I) :
    ∃ (T' : Type) (_ : CommRing T') (_ : IsDomain T') (_ : IsDiscreteValuationRing T')
      (σ : T →+* T') (ρ' : T' →+* Ω) (j' : T' →+* F), IsLocalHom ρ' ∧ ρ'.comp σ = ρ ∧
      Function.Injective j' ∧ j'.comp σ = j ∧ (∀ π : T, Irreducible π → Irreducible (σ π)) ∧
      ∀ i ∈ s, ∃ l : Sp T' ⟶ X, spMap ρ' ≫ l = g i ∧ l ≫ f = spMap σ ≫ h i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨T, _, ‹_›, ‹_›, RingHom.id T, ρ, j, hρ, rfl, hj, rfl, fun _ h => h, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T₁, _, _, _, σ₁, ρ₁, j₁, h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨T₂, _, _, _, σ₂, ρ₂, j₂, k1, k2, k3, k4, k5, l, k6, k7⟩ :=
      GlobalTheory.TorsionUnram.exists_lift_one f ρ₁ h1 j₁ h3 (spMap σ₁ ≫ h a) (g a)
        (by rw [w, ← h2, GlobalTheory.TorsionUnram.spMap_comp', Category.assoc])
    refine ⟨T₂, _, ‹_›, ‹_›, σ₂.comp σ₁, ρ₂, j₂, k1, by rw [← RingHom.comp_assoc, k2, h2], k3,
      by rw [← RingHom.comp_assoc, k4, h4], fun π hπ => k5 _ (h5 π hπ), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨l, k6, by rw [k7, GlobalTheory.TorsionUnram.spMap_comp', Category.assoc]⟩
    · obtain ⟨l₁, e1, e2⟩ := h6 i hi
      exact ⟨spMap σ₂ ≫ l₁, by rw [← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', k2, e1],
        by rw [Category.assoc, e2, GlobalTheory.TorsionUnram.spMap_comp', Category.assoc]⟩

end GlobalTheory.DivPtsUnram

namespace GlobalTheory.DivPtsUnram

theorem pow_eq_comp_mulA {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (b : T ⟶ A) (r : ℕ) :
    b ^ r = b ≫ mulA A r :=
  (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm

theorem unramSub_range {V T F : Type} [CommRing V] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field F]
    (iV : V →+* F) (σ : V →+* T) (j : T →+* F) (hj : Function.Injective j) (hjσ : j.comp σ = iV)
    (hσ : ∀ π : V, Irreducible π → Irreducible (σ π)) : UnramSub iV j.range := by
  let e : T ≃+* j.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hj)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom.comp σ, fun v => ?_,
    fun π hπ => (hσ π hπ).map e⟩
  show j (σ v) = iV v
  rw [← hjσ]; rfl

theorem factor_range {T F : Type} [CommRing T] [Field F] (j : T →+* F) (hj : Function.Injective j) {X : Scheme.{0}}
    (l : Sp T ⟶ X) : ∃ u : Sp j.range ⟶ X, spMap j.range.subtype ≫ u = spMap j ≫ l := by
  let e : T ≃+* j.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hj)
  refine ⟨spMap e.toRingHom ≫ l, ?_⟩
  rw [← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp']
  rfl

end GlobalTheory.DivPtsUnram

namespace GlobalTheory.DivPtsUnram

theorem exists_unram (hL : MulNSt) {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
    [IsAlgClosed F] (iV : V →+* F) (hiV : Function.Injective iV) (P : PolAV (Sp V)) (k : ℕ) (hk : IsUnit (k : V))
    {I : Type} [Finite I] (s : I → (Sp V ⟶ P.A.left)) (hs : ∀ i, s i ≫ P.A.hom = 𝟙 _) :
    ∃ T₁ : Subring F, UnramSub iV T₁ ∧
      (∀ z : Over.mk (spMap iV) ⟶ P.A, z ^ k = 1 → ∃ u : Sp T₁ ⟶ P.A.left, spMap T₁.subtype ≫ u = z.left) ∧
      ∀ i, ∃ u : Sp T₁ ⟶ P.A.left, spMap T₁.subtype ≫ u ≫ (mulA P.A k).left = spMap iV ≫ s i := by
  classical
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (by simpa using hk) (not_isUnit_zero (M₀ := V))
    · exact h
  have hkΓ : IsUnit (k : Γ(Sp V, ⊤)) := by
    simpa using hk.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨hfin, -, -, het, hcard⟩ := hL (Sp V) P k hk1
  have := het hkΓ
  let Ω := AlgebraicClosure (IsLocalRing.ResidueField V)
  let ρ : V →+* Ω := (algebraMap (IsLocalRing.ResidueField V) Ω).comp (IsLocalRing.residue V)
  have hρ : IsLocalHom ρ := inferInstance
  have hkΩ : (k : Ω) ≠ 0 := by simpa using (hk.map ρ).ne_zero
  have hkF : (k : F) ≠ 0 := by simpa using (hk.map iV).ne_zero
  have hk0 : k ^ (2 * P.g) ≠ 0 := pow_ne_zero _ (by omega)
  have c₁ := hcard Ω (spMap ρ) hkΩ
  have c₂ := hcard F (spMap iV) hkF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ hk0)
  have := Nat.finite_of_card_ne_zero (c₂ ▸ hk0)
  let Tc := {x : Over.mk (spMap ρ) ⟶ P.A // x ^ k = 1}
  have := Fintype.ofFinite Tc
  have := Fintype.ofFinite I
  let a₀ : I → (Over.mk (spMap ρ) ⟶ P.A) := fun i => Over.homMk (spMap ρ ≫ s i) (by
    show (spMap ρ ≫ s i) ≫ P.A.hom = spMap ρ
    rw [Category.assoc, hs, Category.comp_id])
  choose b hb using fun i => GlobalTheory.IntegralJets.exists_root (spMap ρ) hL P (a₀ i) k hk1
  let h : Tc ⊕ I → (Sp V ⟶ P.A.left) := Sum.elim (fun _ => η[P.A].left) s
  let g : Tc ⊕ I → (Sp Ω ⟶ P.A.left) := Sum.elim (fun x => x.1.left) (fun i => (b i).left)
  have w : ∀ j, g j ≫ (mulA P.A k).left = spMap ρ ≫ h j := by
    rintro (x | i)
    · have e := congrArg (fun q => q.left) ((pow_eq_comp_mulA P.A x.1 k).symm.trans x.2)
      simpa [g, h, Hom.one_def] using e
    · have e := congrArg (fun q => q.left) ((pow_eq_comp_mulA P.A (b i) k).symm.trans (hb i))
      simpa [g, h, a₀] using e
  obtain ⟨T', _, _, _, σ, ρ', j', h1, h2, h3, h4, h5, h6⟩ :=
    exists_lift_finset (mulA P.A k).left ρ hρ iV hiV h g w Finset.univ
  choose l hl hl' using fun j => h6 j (Finset.mem_univ j)
  refine ⟨j'.range, unramSub_range iV σ j' h3 h4 h5, fun z hz => ?_, fun i => ?_⟩
  · let Tg := {z : Over.mk (spMap iV) ⟶ P.A // z ^ k = 1}
    have hη : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
    have hlA : ∀ x : Tc, l (Sum.inl x) ≫ P.A.hom = spMap σ := fun x => by
      rw [← Over.w (mulA P.A k), ← Category.assoc, hl']
      simp [h, hη]
    let Φ : Tc → Tg := fun x => ⟨Over.homMk (spMap j' ≫ l (Sum.inl x)) (by
        show (spMap j' ≫ l (Sum.inl x)) ≫ P.A.hom = spMap iV
        rw [Category.assoc, hlA, ← GlobalTheory.TorsionUnram.spMap_comp', h4]), by
      rw [pow_eq_comp_mulA]
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [hl', ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', h4]
      simp [h, Hom.one_def]⟩
    have hΦ : Function.Injective Φ := fun a c hac => by
      have e : l (Sum.inl a) = l (Sum.inl c) :=
        GlobalTheory.eq_of_preconnected_of_unramified (mulA P.A k).left ((hl' (Sum.inl a)).trans (hl' (Sum.inl c)).symm)
          (spMap j') congr((($hac).1).left)
      exact Subtype.ext (Over.OverMorphism.ext ((hl (Sum.inl a)).symm.trans (e ▸ hl (Sum.inl c))))
    have hΦ' := (hΦ.bijective_of_nat_card_le (c₂.trans c₁.symm).le).2
    obtain ⟨x, hx⟩ := hΦ' ⟨z, hz⟩
    obtain ⟨u, hu⟩ := factor_range j' h3 (l (Sum.inl x))
    refine ⟨u, hu.trans ?_⟩
    exact congr((($hx).1).left)
  · obtain ⟨u, hu⟩ := factor_range j' h3 (l (Sum.inr i))
    refine ⟨u, ?_⟩
    rw [← Category.assoc, hu, Category.assoc, hl', ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', h4]
    rfl

end GlobalTheory.DivPtsUnram

namespace GlobalTheory.DivPtsUnram

theorem spMap_eq_of_subring {V F : Type} [CommRing V] [Field F] (iV : V →+* F) (T₁ : Subring F) (f₁ : V →+* T₁)
    (hf₁ : ∀ v, (f₁ v : F) = iV v) (a : Sp T₁ ⟶ Sp V) (ha : spMap T₁.subtype ≫ a = spMap iV) : a = spMap f₁ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective a
  have e : ψ ≫ CommRingCat.ofHom T₁.subtype = CommRingCat.ofHom iV := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact ha
  have e' : ψ = CommRingCat.ofHom f₁ := by
    ext v
    show ((ψ.hom v : T₁) : F) = (f₁ v : F)
    rw [hf₁]
    exact congr($e v)
  rw [e']

theorem pow_b {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} (p : QkPt D F k) : p.g.b ^ k = DegPre.cF D F p.y := by
  obtain ⟨hh, ⟨gs, h0, hadd, hlast⟩, hiota⟩ := p.eq
  have key : ∀ i : ℕ, ∀ hi : i < k + 1, (gs ⟨i, hi⟩).b = p.g.b ^ i := by
    intro i
    induction i with
    | zero => intro hi; rw [pow_zero, Hom.one_def]; exact h0.1
    | succ i ih =>
      intro hi
      have e := (hadd ⟨i, by omega⟩).1
      rw [pow_succ, ← ih (by omega), Hom.mul_def]
      exact e
  rw [← hiota.1, ← hlast]
  exact (key k (by omega)).symm

end GlobalTheory.DivPtsUnram

namespace GlobalTheory.DivPtsUnram

theorem divPts_unram : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∃ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ ∧ ∀ p : QkPt D (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left := by
  intro R _ _ D V _ _ _ φ hV _ hcomp k hk
  obtain ⟨_, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  let F := AlgebraicClosure (FractionRing V)
  let iV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hiV : Function.Injective iV :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨P', gP, hg, -, hmul, -⟩ := hL.polBaseChange (Sp R) (Sp V) (spMap φ) D.P
  have := P'.isAb.comm
  have htF : (TF (R := R) F).hom = spMap iV ≫ spMap φ := by
    show spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) = spMap iV ≫ spMap φ
    rw [← GlobalTheory.TorsionUnram.spMap_comp', ← GlobalTheory.TorsionUnram.spMap_comp']
    congr 1
    ext r
    exact hcomp r

  have hcw : ∀ y : D.X, (D.c y).left ≫ D.P.A.hom = 𝟙 (Sp R) := fun y => Over.w (D.c y)
  let s : D.X → (Sp V ⟶ P'.A.left) := fun y =>
    hg.lift (spMap φ ≫ (D.c y).left) (𝟙 _) (by rw [Category.assoc, hcw, Category.comp_id, Category.id_comp])
  have hs : ∀ y, s y ≫ P'.A.hom = 𝟙 _ := fun y => hg.lift_snd _ _ _
  let bX := Module.Free.chooseBasis ℤ D.X
  obtain ⟨T₁, hT₁, htors, hdiv⟩ := exists_unram hL.mulN iV hiV P' k hk (fun i => s (bX i)) (fun i => hs _)
  have hT₁' := hT₁
  obtain ⟨_, f₁, hf₁, -⟩ := hT₁

  let KP : Over (Sp V) := Over.mk (spMap iV)
  have hinc : spMap T₁.subtype ≫ spMap f₁ = spMap iV := by
    rw [← GlobalTheory.TorsionUnram.spMap_comp']
    congr 1
    ext v
    exact hf₁ v
  let inc : KP ⟶ Over.mk (spMap f₁) := Over.homMk (spMap T₁.subtype) hinc
  let Φ : (Over.mk (spMap f₁) ⟶ P'.A) →* (KP ⟶ P'.A) :=
    { toFun := fun w => inc ≫ w
      map_one' := by rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (inc ≫ toUnit _) (toUnit _)]
      map_mul' := fun w w' => MonObj.comp_mul inc w w' }
  have mem : ∀ z : KP ⟶ P'.A, (∃ u : Sp T₁ ⟶ P'.A.left, spMap T₁.subtype ≫ u = z.left) → z ∈ Φ.range := by
    rintro z ⟨u, hu⟩
    have hw : u ≫ P'.A.hom = spMap f₁ := spMap_eq_of_subring iV T₁ f₁ hf₁ _ (by
      rw [← Category.assoc, hu]
      exact Over.w z)
    exact ⟨Over.homMk u hw, Over.OverMorphism.ext hu⟩

  let C : D.X → (KP ⟶ P'.A) := fun y => Over.homMk (spMap iV ≫ s y) (by
    show (spMap iV ≫ s y) ≫ P'.A.hom = spMap iV
    rw [Category.assoc, hs, Category.comp_id])

  let tb : (KP ⟶ P'.A) →* (Over.mk (spMap iV ≫ spMap φ) ⟶ D.P.A) := MonoidHom.mk' (toBase hg.w) (hmul KP)
  have tb_left : ∀ z, (tb z).left = z.left ≫ gP := fun z => rfl
  have tb_inj : Function.Injective tb := fun z z' e => by
    refine Over.OverMorphism.ext (hg.hom_ext ?_ ?_)
    · rw [← tb_left, ← tb_left, e]
    · exact (Over.w z).trans (Over.w z').symm
  have tbC : ∀ y, tb (C y) = toUnit _ ≫ D.c y := fun y => by
    refine Over.OverMorphism.ext ?_
    rw [tb_left]
    simp only [C, Over.homMk_left, Category.assoc, s, IsPullback.lift_fst, Over.comp_left]
    rfl
  have C_add : ∀ a b, C (a + b) = C a * C b := fun a b => tb_inj (by
    rw [map_mul, tbC, tbC, tbC, D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul])
  have C_zero : C 0 = 1 := by
    have e := C_add 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have C_neg : ∀ a, C (-a) = (C a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← C_add, add_neg_cancel, C_zero])
  have hβ : ∀ i, ∃ w ∈ Φ.range, w ^ k = C (bX i) := fun i => by
    obtain ⟨u, hu⟩ := hdiv i
    have hover : (spMap T₁.subtype ≫ u) ≫ P'.A.hom = spMap iV := by
      rw [← Over.w (mulA P'.A k)]
      simp only [Category.assoc]
      rw [reassoc_of% hu]
      simp [hs]
    refine ⟨Over.homMk (spMap T₁.subtype ≫ u) hover, mem _ ⟨u, rfl⟩, ?_⟩
    rw [pow_eq_comp_mulA]
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, C]
    exact hu
  choose β hβH hβk using hβ
  let S : AddSubgroup D.X :=
    { carrier := {y | ∃ w ∈ Φ.range, w ^ k = C y}
      add_mem' := by
        rintro a b ⟨w, hw, ha⟩ ⟨w', hw', hb⟩
        exact ⟨w * w', mul_mem hw hw', by rw [mul_pow, ha, hb, C_add]⟩
      zero_mem' := ⟨1, one_mem _, by rw [one_pow, C_zero]⟩
      neg_mem' := by
        rintro a ⟨w, hw, ha⟩
        exact ⟨w⁻¹, inv_mem hw, by rw [inv_pow, ha, C_neg]⟩ }
  have hS : ∀ y, y ∈ S := fun y => by
    rw [← bX.sum_repr y]
    exact S.sum_mem fun i _ => S.zsmul_mem ⟨β i, hβH i, hβk i⟩ _
  refine ⟨T₁, hT₁', fun p => ?_⟩
  let eTF : Over.mk (spMap iV ≫ spMap φ) ⟶ TF (R := R) F := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (TF (R := R) F).hom = spMap iV ≫ spMap φ
    rw [Category.id_comp, htF])
  let X₀ := eTF ≫ p.g.b
  have hX₀ : X₀ ^ k = toUnit _ ≫ D.c p.y := by
    show (eTF ≫ p.g.b) ^ k = _
    rw [← MonObj.comp_pow, GlobalTheory.DivPtsUnram.pow_b, DegPre.cF, ← Category.assoc,
      toUnit_unique (eTF ≫ toUnit _) (toUnit _)]
  let z : KP ⟶ P'.A := Over.homMk (hg.lift X₀.left (spMap iV) (Over.w X₀)) (hg.lift_snd _ _ _)
  have hz : tb z = X₀ := Over.OverMorphism.ext (by rw [tb_left]; exact hg.lift_fst _ _ _)
  have hzk : z ^ k = C p.y := tb_inj (by rw [map_pow, hz, hX₀, tbC])
  obtain ⟨w, hw, hwk⟩ := hS p.y
  have ht : (z * w⁻¹) ^ k = 1 := by rw [mul_pow, inv_pow, hzk, hwk, mul_inv_cancel]
  have hzw : z * w⁻¹ ∈ Φ.range := mem _ (htors _ ht)
  obtain ⟨w', hw'⟩ : z ∈ Φ.range := by simpa using mul_mem hzw hw
  refine ⟨w'.left ≫ gP, ?_⟩
  have e1 : spMap T₁.subtype ≫ w'.left = z.left := congrArg (fun q => q.left) hw'
  rw [← Category.assoc, e1, ← tb_left, hz]
  simp [X₀, eTF]

end GlobalTheory.DivPtsUnram
