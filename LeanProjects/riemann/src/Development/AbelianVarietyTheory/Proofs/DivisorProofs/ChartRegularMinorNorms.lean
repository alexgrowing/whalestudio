import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMatricesValueMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionEquivRegularUnitValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame.MaxFun

section Local

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem unitAt_prod_div {x : Z} {k : ℕ} (m : ℕ) {u s : Fin k → Z.functionField} (hu : ∀ i, UnitAt x (u i))
    (hs : ∀ i, UnitAt x (s i)) : UnitAt x (∏ i, u i ^ m / s i) := by
  refine Finset.prod_induction _ (UnitAt x) (fun a b ha hb => ha.mul hb) ⟨1, isUnit_one, map_one _⟩ fun i _ => ?_
  rw [div_eq_mul_inv]
  refine UnitAt.mul ?_ (hs i).inv
  obtain ⟨a, ha, e⟩ := hu i
  exact ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩

theorem regAt_pow_mul {x : Z} {m : ℕ} (hm : 0 < m) {a b : Z.functionField} (ha : RegAt x a) (hb : UnitAt x b) :
    RegAt x (a ^ m * b) ∧ (UnitAt x (a ^ m * b) ↔ UnitAt x a) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have hinj : Function.Injective (algebraMap (Z.presheaf.stalk x) Z.functionField) := IsFractionRing.injective _ _
  have key : ∀ c : Z.presheaf.stalk x, UnitAt x (algebraMap _ Z.functionField c) ↔ IsUnit c := fun c =>
    ⟨fun ⟨_, h, e⟩ => hinj e ▸ h, fun h => ⟨c, h, rfl⟩⟩
  rw [← map_pow, ← map_mul, key, key, IsUnit.mul_iff, isUnit_pow_iff hm.ne']
  exact ⟨⟨_, rfl⟩, fun h => h.1, fun h => ⟨h, hb⟩⟩

theorem valAt_ne_zero {K : Type} [Field K] (z : Sp K ⟶ Z) {a : Z.functionField} (ha : UnitAt (below z) a) :
    valAt z a ≠ 0 := (Base.valAt_zpow z ha).1

theorem valAt_pow_mul {K : Type} [Field K] (z : Sp K ⟶ Z) {k : ℕ} (m : ℕ) {a : Z.functionField}
    {u s : Fin k → Z.functionField} (ha : RegAt (below z) a) (hu : ∀ i, UnitAt (below z) (u i))
    (hs : ∀ i, UnitAt (below z) (s i)) :
    valAt z (a ^ m * ∏ i, u i ^ m / s i) = valAt z a ^ m * ∏ i, valAt z (u i) ^ m / valAt z (s i) := by
  obtain ⟨a, rfl⟩ := ha
  choose u' hu' eu using hu
  choose s' hs' es using hs
  have e {S : Type} [Field S] (ψ : Z.presheaf.stalk (below z) →+* S) :
      ψ a ^ m * ∏ i, ψ (u' i) ^ m / ψ (s' i) = ψ (a ^ m * ∏ i, u' i ^ m * ((hs' i).unit⁻¹ : _ˣ)) := by
    rw [map_mul, map_pow, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_units_inv, div_eq_mul_inv, IsUnit.unit_spec]
  simp only [← eu, ← es]
  rw [e]
  simp only [Base.valAt_stalk]
  exact (e _).symm

end Local

theorem pow_div_eq {m : ℕ} {l a b n n' : ℝ} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) (hn' : 0 < n')
    (h1 : m * l = Real.log b) (h2 : l = Real.log a + Real.log n' - Real.log n) : a ^ m / b = (n / n') ^ m := by
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_div (by positivity) hb.ne', Real.log_pow, Real.log_pow, Real.log_div hn.ne' hn'.ne', ← h1, h2]
  ring

theorem prod_div_succ (ν : ℕ → ℝ) (h : ∀ i, ν i ≠ 0) (k : ℕ) : ∏ i : Fin k, ν i / ν ((i : ℕ) + 1) = ν 0 / ν k := by
  induction k with
  | zero => simp [h]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    field_simp [h]

theorem minor_pow_div {K L : Type} [Field K] [Field L] (φ : K →+* L) {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) L)
    (T : Matrix (Fin g) (Fin g) K) (d : Fin g → Kˣ) (hT : T.BlockTriangular id) (hd : ∀ i, T i i = d i) (m : ℕ)
    (γ : Fin g → K) (r : Fin g → L) (hγ : ∀ i, φ (γ i ^ m) * r i ≠ 0) (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) :
    minorAt H k hk τ ^ m / ∏ i : Fin k, r (Fin.castLE hk i) = minorAt (H * (T.map φ)⁻¹) k hk τ ^ m *
      ∏ i : Fin k, φ (γ (Fin.castLE hk i) * d (Fin.castLE hk i)) ^ m /
        (φ (γ (Fin.castLE hk i) ^ m) * r (Fin.castLE hk i)) := by
  rw [minorAt_triChange H (T.map φ) (fun i j h => by rw [Matrix.map_apply, hT h, map_zero])
    (fun i => by rw [Matrix.map_apply, hd]; exact (map_ne_zero φ).2 (d i).ne_zero) k hk τ, mul_pow, mul_div_assoc,
    ← Finset.prod_pow, ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := left_ne_zero_of_mul (hγ (Fin.castLE hk i))
  rw [Matrix.map_apply, hd, map_mul, mul_pow, ← map_pow φ (γ _), mul_div_mul_left _ _ h]

theorem exists_maxFun : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime → ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → LineBase V d A p → ChartReg V U H T → MinorNorm V W U H d T A p → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U₁ : V.X.Opens) (m : ℕ) (f : ∀ k : ℕ, (Fin k → Fin (g + g)) → V.X.functionField), 0 < m ∧ U₁ ≤ U ∧ x ∈ U₁ ∧ (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) (z : V.G), V.j z ∈ U₁ → RegAt (V.j z) (f k τ) ∧ (UnitAt (V.j z) (f k τ) ↔ UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ))) ∧ (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U₁ → ∀ (k : ℕ) (hk : k ≤ g), 0 < colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k) ∧ ∀ τ : Fin k → Fin (g + g), e.w (valAt (z ≫ V.j) (f k τ)) = (e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) / colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k)) ^ m) := by
  intro F _ _ Y C g A p _ V W _ U H d T hT hL hR hM x hx _
  obtain ⟨hd, L, m, hm, hLN⟩ := hL
  have hc : ∀ i, ∃ c, x ∈ (L i).U c := fun i => by
    have : x ∈ ⨆ c, (L i).U c := by rw [(hLN i).1.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose c hc using hc
  choose r _ hru hrn using fun i => (hLN i).2
  let U₁ : V.X.Opens := U ⊓ Finset.univ.inf fun i => (L i).U (c i)
  have hU₁ : ∀ i, U₁ ≤ (L i).U (c i) := fun i => inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  let ρ : Fin g → V.G.functionField := fun i => r i fun _ => c i
  have hs : ∀ z : V.G, V.j z ∈ U₁ → ∀ i, UnitAt z (V.φ (genAt (A i).D (V.π z) ^ m) * ρ i) := fun z hz i => by
    refine hru i (fun _ => c i) z ?_
    change z ∈ LB.wchart (L i) (fun _ : PUnit => V.j) fun _ => c i
    have h1 : V.j z ∈ (L i).U (c i) := hU₁ i hz
    simpa [LB.wchart] using h1
  have hu : ∀ (z : V.G) i, UnitAt z (V.φ (genAt (A i).D (V.π z) * d (V.π z) i)) := fun z i => V.unitAt_φ (hd i _)
  have ha : ∀ z : V.G, V.j z ∈ U₁ → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)),
      RegAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ) := fun z hz k hk τ => by
    obtain ⟨B, hB⟩ := CramerValues.exists_germ_matrix _ (hR z hz.1)
    rw [hB, CramerValues.minorAt_map_ringHom]
    exact ⟨_, rfl⟩
  let f : ∀ k : ℕ, (Fin k → Fin (g + g)) → V.X.functionField := fun k τ =>
    if hk : k ≤ g then (fnEquiv V).symm (minorAt H k hk τ ^ m / ∏ i : Fin k, ρ (Fin.castLE hk i)) else 0
  have hf : ∀ z : V.G, V.j z ∈ U₁ → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)),
      fnEquiv V (f k τ) = minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ ^ m *
        ∏ i : Fin k, V.φ (genAt (A (Fin.castLE hk i)).D (V.π z) * d (V.π z) (Fin.castLE hk i)) ^ m /
          (V.φ (genAt (A (Fin.castLE hk i)).D (V.π z) ^ m) * ρ (Fin.castLE hk i)) := fun z hz k hk τ => by
    simp only [f, dif_pos hk, RingEquiv.apply_symm_apply]
    exact minor_pow_div V.φ H (T (V.π z)) (d (V.π z)) (hT _).1 (hT _).2 m (fun i => genAt (A i).D (V.π z)) ρ
      (fun i => (hs z hz i).ne_zero) k hk τ
  have hreg : ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) (z : V.G), V.j z ∈ U₁ → RegAt (V.j z) (f k τ) ∧
      (UnitAt (V.j z) (f k τ) ↔ UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ)) := fun k hk τ z hz => by
    obtain ⟨h1, h2⟩ := (fnEquiv_transport V).1 z (f k τ)
    rw [← h1, ← h2, hf z hz k hk τ]
    exact regAt_pow_mul hm (ha z hz k hk τ) (unitAt_prod_div m (fun i => hu z _) fun i => hs z hz _)
  refine ⟨U₁, m, f, hm, inf_le_left, ⟨hx, ?_⟩, hreg, ?_⟩
  · have : ∀ s : Finset (Fin g), x ∈ s.inf fun i => (L i).U (c i) := fun s => by
      induction s using Finset.induction_on with
      | empty => trivial
      | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hc a, ih⟩
    exact this _
  intro v hv e y hy z yt hz hyt htop
  have hb : below y.1 = V.π (below z) := by rw [← hz]; rfl
  have hj : V.j (below z) ∈ U₁ := by
    have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U₁ := by
      rw [← hyt]
      exact htop (Set.mem_univ ((spMap e.O.subtype) (IsLocalRing.closedPoint _)))
    exact h1
  obtain ⟨hpos, hlg⟩ := hM v hv e y hy z yt hz hyt (htop.trans ((Scheme.Hom.preimage_mono yt) inf_le_left))
  have hall := ((MinorQuot.colMinor_pos_and_quotient e.w (isNonarchimedean_w e) (valMat V H (T (below y.1)) z)).2
    ((MinorQuot.colMinor_pos_and_quotient e.w (isNonarchimedean_w e) (valMat V H (T (below y.1)) z)).1.1 hpos)).1
  intro k hk
  refine ⟨hall _, fun τ => ?_⟩
  set ν : ℕ → ℝ := fun n => colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < n)
    with hν
  have hν0 : ν 0 = 1 := by simp [hν, colMinor_empty]
  have hq : ∀ i : Fin g, e.w (valAt z (V.φ (genAt (A i).D (V.π (below z)) * d (V.π (below z)) i))) ^ m /
      e.w (valAt z (V.φ (genAt (A i).D (V.π (below z)) ^ m) * ρ i)) = (ν i / ν ((i : ℕ) + 1)) ^ m := fun i => by
    have h1 := hrn i v hv e y trivial z yt (fun _ => c i) hz hyt (htop.trans ((Scheme.Hom.preimage_mono yt) (hU₁ i)))
    have h2 := hlg i
    have e1 : Finset.Iic i = Finset.univ.filter fun l : Fin g => (l : ℕ) < (i : ℕ) + 1 := by
      ext l; simp [Nat.lt_succ_iff]
    have e2 : Finset.Iio i = Finset.univ.filter fun l : Fin g => (l : ℕ) < (i : ℕ) := by
      ext l; simp
    have e3 : valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i) =
        valAt z (V.φ (genAt (A i).D (V.π (below z)) * d (V.π (below z)) i)) := by
      rw [V.valAt_φ z (hd i _).regAt, hz, hb]
    rw [e1, e2, e3] at h2
    beta_reduce at h1
    rw [hb] at h1
    exact pow_div_eq (e.w.pos (valAt_ne_zero z (hu _ i))) (e.w.pos (valAt_ne_zero z (hs _ hj i))) (hall _) (hall _) h1 h2
  have hv1 : minorAt (valMat V H (T (below y.1)) z) k hk τ =
      valAt z (minorAt (H * ((T (V.π (below z))).map V.φ)⁻¹) k hk τ) := by
    rw [((CramerValues.values_regular z).2.1 _ (hR _ hj.1) k hk τ).2, hb]
    rfl
  rw [← (fnEquiv_transport V).2 z _ (hreg k hk τ _ hj).1, hf _ hj k hk τ,
    valAt_pow_mul z m (ha _ hj k hk τ) (fun i => hu _ _) (fun i => hs _ hj _), hv1, map_mul, map_pow, map_prod]
  simp only [map_div₀, map_pow e.w, hq, Fin.val_castLE]
  rw [Finset.prod_pow, prod_div_succ ν (fun i => (hall _).ne') k, hν0, ← mul_pow, mul_one_div]

end GlobalTheory.ConstLat.CramerFrame.MaxFun

end
