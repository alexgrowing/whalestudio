import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPushedTraitPointLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ToricTorsionCompare

theorem units_of_pow_eq_one : ∀ (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ), 1 ≤ k →
    ∀ (τ : Multiplicative X →* Kˣ), τ ^ k = 1 → ∃ τO : Multiplicative X →* Oˣ, ∀ x, ((τO x : O) : K) = (τ x : K) := by
  intro K _ O X _ k hk τ hτ
  have hpow : ∀ x, (τ x : K) ^ k = 1 := fun x => by
    have := congrArg (fun f => ((f x : Kˣ) : K)) hτ
    simpa [MonoidHom.pow_apply] using this
  have mem : ∀ x, (τ x : K) ∈ O := fun x => by
    rcases O.mem_or_inv_mem (τ x : K) with h | h
    · exact h
    · have h1 : (τ x : K) ^ (k - 1) * (τ x : K) = 1 := by rw [← pow_succ, Nat.sub_add_cancel hk, hpow]
      have h2 : ((τ x : K)⁻¹) ^ (k - 1) = τ x := by rw [inv_pow, inv_eq_of_mul_eq_one_right h1]
      rw [← h2]; exact O.pow_mem h _
  have vi : ∀ x, (τ x : K) * (τ x⁻¹ : K) = 1 := fun x => by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  let f : Multiplicative X → Oˣ := fun x =>
    ⟨⟨τ x, mem x⟩, ⟨τ x⁻¹, mem x⁻¹⟩, Subtype.ext (vi x), Subtype.ext ((mul_comm _ _).trans (vi x))⟩
  exact ⟨MonoidHom.mk' f (fun x y => Units.ext (Subtype.ext (by simp [f]))), fun x => rfl⟩

theorem toric_torsion_eq_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' _ _ hR hW g m V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hb hc hd he hf F _ _ _ _ O φ hφ hφW hgF k hk τ τ' q q' v v' hτ'k hττ' hqy hq hq'y hq' hv hv'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H R t P hR k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H W t' P' hW k hk1
  obtain ⟨fR, hfR, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨fW, hfW, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {G : Type} [CommGroup G] (f : Multiplicative P'.D.toPre.X →* G), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  have hv0 : v = (s F _ τ hτk).left :=
    ((hfR q v).1 hv).trans ((hfR q _).1 (s4 F _ τ hτk q rfl hqy hq)).symm
  have hv0' : v' = (s' F _ τ' hτ'k).left :=
    ((hfW q' v').1 hv').trans ((hfW q' _).1 (s4' F _ τ' hτ'k q' rfl hq'y hq')).symm

  obtain ⟨τO, hτO⟩ := units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl

  let bW : ResidueField W →+* Ω := Ideal.Quotient.lift (maximalIdeal W) β hβ
  obtain ⟨Ω', _, _, σ, κ₀, hσκ⟩ : ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (σ : Ω →+* Ω')
      (κ₀ : ResidueField O →+* Ω'), σ.comp bW = κ₀.comp (ResidueField.map φ) := by
    letI := bW.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (ResidueField W) Ω (ResidueField O))
    letI := Ideal.Quotient.field M
    let q0 : TensorProduct (ResidueField W) Ω (ResidueField O) →+* AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) :=
      (algebraMap (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) _).comp (Ideal.Quotient.mk M)
    refine ⟨AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M), inferInstance, inferInstance,
      q0.comp Algebra.TensorProduct.includeLeftRingHom, q0.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg q0.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  let κ : O →+* Ω' := κ₀.comp (residue O)
  have hκ : σ.comp β = κ.comp φ := by
    ext w
    have := congrArg (fun f => f (residue W w)) hσκ
    change σ (bW (residue W w)) = κ₀ (ResidueField.map φ (residue W w)) at this
    rw [ResidueField.map_residue] at this
    exact this
  have hκloc : IsLocalHom κ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : residue O a = 0 := (residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 hna)
    have h0 : κ a = 0 := by simp only [κ, RingHom.comp_apply, this, map_zero]
    rw [h0] at ha; exact not_isUnit_zero ha

  obtain ⟨U, hU, hUloc⟩ := IsLocalRing.exists_factor_valuationRing (σ.comp α)
  let u : V →+* U := (σ.comp α).codRestrict U.toSubring hU
  have hwu : U.subtype.comp u = σ.comp α := rfl
  let τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ := (Units.map κ.toMonoidHom).comp τO
  have h'' : τ'' ^ k = 1 := by
    rw [show τ'' ^ k = (Units.map κ.toMonoidHom).comp (τO ^ k) by ext x; simp [τ'']]
    rw [hτOk]; ext; simp
  obtain ⟨τU, hτU⟩ := units_of_pow_eq_one Ω' U _ k hk1 τ'' h''
  have hτUk : τU ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Ω'ˣ) : Ω')) h''
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτU, this]; rfl
  let zU : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom.toMonoidHom).comp τU)
  have hzU : ∀ χ, GlobalTheory.UU.chV zU χ = unitOn (τU (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, zU, MulEquiv.apply_symm_apply]; rfl
  have hkU : IsUnit (k : U) := by simpa using hk.map (u.comp ψ)
  let τRU := τU.comp ρm
  have hτRU : τRU ^ k = 1 := by
    exact powc τU hτUk
  have hG1 := GlobalTheory.T.toricTorsionSection_eq_pushed_trait_point_local E H R t P k s s1 s2 s3 _ ρ V ψ tV mV j t₀ m₀ h₀ m₀' hc hd U u hUloc hkU τU τRU hτRU hτUk
    (fun χ => rfl) zU hzU
  have hG2 := GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field E H W t' P' k s' s3' R t g m V ψ tV mV Ω α β hβ tΩ n n' j hb hf Ω' σ (κ.comp φ) hκ.symm
    U u U.subtype hwu τU τ'' h'' (fun χ => (hτU χ).symm) zU hzU
  let τRΩ := τ''.comp ρm
  have hτRΩ : τRΩ ^ k = 1 := by
    exact powc τ'' h''
  have hgU : (κ.comp φ).comp g = U.subtype.comp (u.comp ψ) := by
    ext r
    have := congrArg (fun f => σ f) (RingHom.congr_fun he r)
    have h2 := RingHom.congr_fun hκ (g r)
    simp only [RingHom.comp_apply] at this h2 ⊢
    rw [← h2, ← this]; rfl
  have h8 : (s Ω' ((κ.comp φ).comp g) τRΩ hτRΩ).left = spMap U.subtype ≫ (s U (u.comp ψ) τRU hτRU).left :=
    s2 U Ω' _ _ U.subtype τRU hτRU τRΩ hτRΩ hgU (fun χ => (hτU (ρm χ)).symm)

  let τOR := τO.comp ρm
  have hτOR : τOR ^ k = 1 := by
    exact powc τO hτOk
  obtain ⟨e, he'⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap φ)) (spMap (φ.comp g)) (spMap_comp g φ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hxy : s O (φ.comp g) τOR hτOR = e (s' O φ τO hτOk) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' κ hκloc ?_
    · rw [s1, ← map_pow, s1', map_one]
    · rw [he', ← Category.assoc, ← s2' O Ω' φ (κ.comp φ) κ τO hτOk τ'' h'' rfl (fun χ => rfl), hG2,
        ← s2 O Ω' (φ.comp g) ((κ.comp φ).comp g) κ τOR hτOR τRΩ hτRΩ rfl (fun χ => rfl), h8, hG1]
  have hOR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    ext r; simp [hgF, hφW]
  have hOW : (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W)) = O.subtype.comp φ := by
    ext w; simp [hφW]
  rw [hv0, hv0', s2 O F _ _ O.subtype τOR hτOR τ hτk hOR (fun χ => by simp [τOR, hτ, hτO]),
    s2' O F _ _ O.subtype τO hτOk τ' hτ'k hOW (fun χ => by simp [hτO]), hxy, he', Category.assoc]

end GlobalTheory.ToricTorsionCompare
