import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGenericFibreGaloisExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.LevelPrimePower

theorem iterate_fixes {A : Type} [CommGroup A] (f : A →* A) (ℓ : ℕ) (hf : ∀ x, x ^ ℓ = 1 → f x = x) (e : ℕ) :
    ∀ x : A, x ^ ℓ ^ (e + 1) = 1 → f^[ℓ ^ e] x = x := by
  induction e with
  | zero => intro x hx; simpa using hf x (by simpa using hx)
  | succ e ih =>
    intro x hx
    let h : A →* A := ((show Monoid.End A from f) ^ ℓ ^ e : Monoid.End A)
    have hh : ∀ a, h a = f^[ℓ ^ e] a := fun a => congrFun (Monoid.End.coe_pow A f _) a
    have h1 : h x ^ ℓ = x ^ ℓ := by
      rw [← map_pow, hh]
      exact ih _ (by rw [← pow_mul, ← pow_succ', hx])
    have hy : (h x / x) ^ ℓ = 1 := by rw [div_pow, h1, div_self']
    have h2 : h (h x / x) = h x / x := by
      rw [hh]
      exact ih _ (by rw [pow_succ', pow_mul, hy, one_pow])
    have h3 : ∀ n : ℕ, h^[n] x = x * (h x / x) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [Function.iterate_succ_apply', ihn, map_mul, map_pow, h2, pow_succ', ← _root_.mul_assoc,
          mul_div_cancel]
    have h4 : (h : A → A) = f^[ℓ ^ e] := funext hh
    rw [pow_succ, Function.iterate_mul, ← h4, h3, hy, _root_.mul_one]

theorem exists_normal {G A : Type} [Group G] [CommGroup A] (ρ : G → A →* A) (h1 : ∀ x, ρ 1 x = x)
    (hm : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x)) (ℓ e : ℕ) (hf : ∀ σ x, x ^ ℓ = 1 → ρ σ x = x) :
    ∃ H : Subgroup G, H.Normal ∧ (∀ σ, σ ^ ℓ ^ e ∈ H) ∧ ∀ σ ∈ H, ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x := by
  let H : Subgroup G :=
    { carrier := {σ | ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x}
      one_mem' := fun x _ => h1 x
      mul_mem' := fun {a b} ha hb x hx => by rw [hm, hb x hx, ha x hx]
      inv_mem' := fun {a} ha x hx => by
        conv_lhs => rw [← ha x hx, ← hm, inv_mul_cancel, h1] }
  refine ⟨H, ⟨fun a ha g x hx => ?_⟩, fun σ x hx => ?_, fun σ hσ => hσ⟩
  · rw [hm, hm, ha _ (by rw [← map_pow, hx, map_one]), ← hm, mul_inv_cancel, h1]
  · have hp : ∀ (n : ℕ) x, ρ (σ ^ n) x = (ρ σ)^[n] x := by
      intro n
      induction n with
      | zero => intro x; simpa using h1 x
      | succ n ih => intro x; rw [pow_succ, hm, ih, Function.iterate_succ_apply]
    rw [hp]
    exact iterate_fixes _ ℓ (hf σ) e x (by rw [pow_succ, pow_mul, hx, one_pow])

theorem exists_factor_fixedField {F L : Type} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {Y : Scheme.{0}} (y : Sp L ⟶ Y) (h : ∀ σ ∈ H, spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp (IntermediateField.fixedField H) ⟶ Y, spMap (algebraMap (IntermediateField.fixedField H) L) ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField L Y).symm ⟨p, φ⟩ = Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ IntermediateField.fixedField H := by
    intro b
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ hσ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict (IntermediateField.fixedField H) hmem)) ≫
    Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_intermediate {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] (s₀ : Sp F ⟶ S) (s : Sp L ⟶ S)
    (hs : s = spMap (algebraMap F L) ≫ s₀) (ℓ e : ℕ) (hℓ : ℓ.Prime) (ζ₀ : F) (hζ : IsPrimitiveRoot ζ₀ ℓ)
    (hfix : ∀ z : Over.mk s ⟶ X, z ^ ℓ = 1 → ∃ w : Sp F ⟶ X.left, spMap (algebraMap F L) ≫ w = z.left) :
    ∃ M : IntermediateField F L, IsGalois F M ∧ (∃ d, Module.finrank F M = ℓ ^ d) ∧
      (∀ u : Lˣ, u ^ ℓ ^ e = 1 → (u : L) ∈ M) ∧
      ∀ z : Over.mk s ⟶ X, z ^ ℓ ^ e = 1 → ∃ w : Sp M ⟶ X.left, spMap (algebraMap M L) ≫ w = z.left := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hσ : ∀ σ : L ≃ₐ[F] L, spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap F L) = spMap (algebraMap F L) := by
    intro σ
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a
  let t : (L ≃ₐ[F] L) → (Over.mk s ⟶ Over.mk s) := fun σ => Over.homMk (spMap σ.toAlgHom.toRingHom) (by
    show spMap σ.toAlgHom.toRingHom ≫ s = s
    rw [hs, ← Category.assoc, hσ])
  let ρ : (L ≃ₐ[F] L) → (Over.mk s ⟶ X) →* (Over.mk s ⟶ X) := fun σ =>
    { toFun := fun x => t σ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  have hρ : ∀ σ x, (ρ σ x).left = spMap σ.toAlgHom.toRingHom ≫ x.left := fun _ _ => rfl
  obtain ⟨H₁, n₁, p₁, f₁⟩ := exists_normal ρ
    (fun x => Over.OverMorphism.ext (by
      rw [hρ]
      exact (congrArg (· ≫ x.left) (Spec.map_id (CommRingCat.of L))).trans (Category.id_comp _)))
    (fun σ τ x => Over.OverMorphism.ext (by
      rw [hρ, hρ, hρ]
      erw [← Category.assoc, ← Spec.map_comp]
      rfl)) ℓ e
    (fun σ x hx => Over.OverMorphism.ext (by
      obtain ⟨w, hw⟩ := hfix x hx
      rw [hρ, ← hw]
      erw [← Category.assoc, hσ]))
  obtain ⟨H₂, n₂, p₂, f₂⟩ := exists_normal (fun σ : L ≃ₐ[F] L => Units.map σ.toAlgHom.toRingHom.toMonoidHom)
    (fun x => rfl) (fun σ τ x => rfl) ℓ e
    (fun σ x hx => Units.ext (by
      have hx' : (x : L) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hx'
      show σ (x : L) = x
      rw [← hi, ← map_pow, σ.commutes]))
  let H := H₁ ⊓ H₂
  haveI : H.Normal := inferInstanceAs (H₁ ⊓ H₂).Normal
  have hP : IsPGroup ℓ ((L ≃ₐ[F] L) ⧸ H) := by
    intro g
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p₁ σ, p₂ σ⟩
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, fun u hu => ?_, fun z hz => ?_⟩
  · obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hP
    refine ⟨d, ?_⟩
    rw [← hd, ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
  · rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => congrArg Units.val (f₂ σ hσ.2 u hu)
  · exact exists_factor_fixedField H _ fun σ hσ => congrArg CommaMorphism.left (f₁ σ hσ.1 z hz)

theorem exists_level_primePower : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro F _ _ R₁ _ emb P₁ ℓ N K hℓ hN hℓN ⟨e, hK⟩ ⟨ζ₀, hζ₀⟩ hsec
  have hK0 : 0 < K := hK ▸ pow_pos hℓ.pos e
  have := P₁.isAb.comm
  obtain ⟨L, _, _, Q₃, φ₃, ζ₃, hfd, hgal, hζ₃, -, h₃, -, ⟨lev⟩⟩ := LevelGalois.exists_level_galois emb P₁ K hK0
  obtain ⟨c, rfl⟩ := hℓN
  have hζ₁ : IsPrimitiveRoot (ζ₀ ^ c) ℓ := hζ₀.pow hN (Nat.mul_comm _ _)
  have hs : spMap ((algebraMap F L).comp emb) = spMap (algebraMap F L) ≫ spMap emb := (GlobalTheory.spMap_comp_spMap _ _).symm
  obtain ⟨M, hMgal, hdeg, hroot, hpts⟩ := exists_intermediate P₁.A (spMap emb) (spMap ((algebraMap F L).comp emb)) hs
    ℓ e hℓ _ hζ₁ (fun z hz => by
      let τ := algebraMap L (AlgebraicClosure L)
      let k : Over.mk (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ⟶ Over.mk (spMap ((algebraMap F L).comp emb)) :=
        Over.homMk (spMap τ) rfl
      obtain ⟨y, hy⟩ := hsec _ _ (k ≫ z) (by rw [← MonObj.comp_pow, pow_mul, hz, one_pow, MonObj.comp_one])
      refine ⟨spMap emb ≫ y.left, spec_map_field_cancel τ _ _ ?_⟩
      have hy' : (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ≫ y.left = spMap τ ≫ z.left :=
        congrArg CommaMorphism.left hy
      rw [← hy', hs]
      simp only [Category.assoc])
  rw [← hK] at hroot hpts
  haveI : CharZero M := (algebraMap F M).charZero_iff (algebraMap F M).injective |>.1 inferInstance
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  let ζ' : M := ⟨ζ₃, hroot ζ₃ hζ₃.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' K :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap M L) (IsPrimitiveRoot.coe_units_iff.2 hζ₃)
      (algebraMap M L).injective
  obtain ⟨ζ, hζe⟩ := hζ'.isUnit hK0.ne'
  have hζ : IsPrimitiveRoot ζ K := IsPrimitiveRoot.coe_units_iff.1 (hζe ▸ hζ')
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre hB ((algebraMap F M).comp emb) P₁
  obtain ⟨Q', ψ, hQ'⟩ := exists_isPolFibre hB (algebraMap M (AlgebraicClosure M)) Q
  refine ⟨M, inferInstance, inferInstance, Q, φ, ζ, inferInstance, hMgal, hdeg, hζ, hQ.1, hQ.2.1, hQ.2.2.symm,
    LevelGalois.nonempty_level_of_rational Q K hK0 ζ hζ Q' ψ hQ' fun y hy => ?_⟩
  let σ := algebraMap M (AlgebraicClosure M)
  let τ' : L →ₐ[M] AlgebraicClosure M := IsAlgClosed.lift
  let τ : L →+* AlgebraicClosure M := τ'.toRingHom
  have hτ : spMap τ ≫ spMap (algebraMap M L) = spMap σ := by
    rw [GlobalTheory.spMap_comp_spMap]
    exact congrArg spMap (RingHom.ext τ'.commutes)
  have hML : spMap (algebraMap M L) ≫ spMap ((algebraMap F M).comp emb) = spMap ((algebraMap F L).comp emb) := by
    rw [GlobalTheory.spMap_comp_spMap]
    rfl
  have hPg : IsGrpPullback Q.A P₁.A (spMap ((algebraMap F M).comp emb)) φ := hQ.2.1
  have hQg : IsGrpPullback Q'.A Q.A (spMap σ) ψ := hQ'.2.1
  let y₀ := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hy₀ : y₀ ^ K = 1 := by simp only [y₀, ← map_pow, hy, map_one]
  let j : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
      Over.mk (((𝟙_ (Over (Sp (AlgebraicClosure M)))).hom ≫ spMap σ) ≫ spMap ((algebraMap F M).comp emb)) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ (𝟙 _ ≫ spMap σ) ≫ _ = spMap τ ≫ _
      rw [Category.id_comp, Category.id_comp, ← hML, ← hτ, Category.assoc])
  let y₁ := j ≫ y₀
  have hy₁ : y₁ ^ K = 1 := by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one]
  have hy₁l : y₁.left = (y.left ≫ ψ) ≫ φ := Category.id_comp _
  let y₂ := (ObjPull.pushEquiv h₃ (Over.mk (spMap τ))).symm y₁
  obtain ⟨a, ha⟩ := lev.span _ (spMap τ) y₂ (by rw [← map_pow, hy₁, map_one])
  rw [← GenSpread.comp_linComb] at ha
  set v := linComb lev.pt (fun i => (a i : ℕ)) with hv
  have hvl : spMap τ ≫ v.left = y₂.left := congrArg CommaMorphism.left ha
  let z : Over.mk (spMap ((algebraMap F L).comp emb)) ⟶ P₁.A := Over.homMk (v.left ≫ φ₃) (by
    rw [Category.assoc, h₃.1.w, ← Category.assoc, Over.w v]
    exact Category.id_comp _)
  let k : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
      Over.mk (spMap ((algebraMap F L).comp emb)) := Over.homMk (spMap τ) rfl
  have hzl : spMap τ ≫ z.left = y₁.left := by
    rw [← ObjPull.pushEquiv_symm_left h₃ _ y₁]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ₃) hvl)
  have hkz : k ≫ z = y₁ := Over.OverMorphism.ext hzl
  have hz : z ^ K = 1 := by
    have h : k ≫ z ^ K = k ≫ 1 := by rw [MonObj.comp_pow, hkz, hy₁, MonObj.comp_one]
    exact Over.OverMorphism.ext (spec_map_field_cancel τ _ _ (congrArg CommaMorphism.left h))
  obtain ⟨w, hw⟩ := hpts z hz
  have hw2 : w ≫ P₁.A.hom = 𝟙 _ ≫ spMap ((algebraMap F M).comp emb) := by
    refine spec_map_field_cancel (algebraMap M L) _ _ ?_
    rw [← Category.assoc, hw, Over.w z, Category.id_comp, hML]
    rfl
  let x : 𝟙_ (Over (Sp M)) ⟶ Q.A := Over.homMk (hPg.1.lift w (𝟙 _) hw2) (hPg.1.lift_snd _ _ _)
  have hxl : x.left ≫ φ = w := hPg.1.lift_fst _ _ _
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← hy₁l, ← hzl, ← hw, ← Category.assoc, hτ]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

end GlobalTheory.LevelPrimePower
