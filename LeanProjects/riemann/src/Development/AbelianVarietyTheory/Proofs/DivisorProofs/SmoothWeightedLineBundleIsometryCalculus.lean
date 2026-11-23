import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.IsomCalc

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
variable {L M : MLine p σ}

theorem isom_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      M.φ.φ (a j) y = L.φ.φ (b j) y + logSq y (W j) (u j)) : L.Isom M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.φ.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.φ.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.φ.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.φ.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := M.φ.trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := L.φ.trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isom_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) → M.φ.φ (a j) y = L.φ.φ j y) : L.Isom M :=
  isom_of_local L.B.U (exists_chart L.φ.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun j y h => by rw [logSq_one h, add_zero]; exact hφ j y h

theorem isom_refl (L : MLine p σ) : L.Isom L :=
  isom_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ => rfl

theorem isom_pull (h : L.Isom M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isom (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h
  refine isom_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w.s (c.1, c.2))) (fun x c c' hc hc' => ?_)
    fun c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.φ.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.φ.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    exact (gm_pull (U := M.B.U c.1 ⊓ L.B.U c.2) (𝟙 Y) π x hc (w.s (c.1, c.2))).trans
      ((gm_isGen hw (𝟙 Y ≫ π) x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2).trans (congrArg (_ * ·)
        (gm_pull (U := M.B.U c'.1 ⊓ L.B.U c'.2) (𝟙 Y) π x hc' (w.s (c'.1, c'.2))).symm))
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine (M.φ.pull_φ π hπ _ y).trans ((h _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) (L.φ.pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

theorem isom_pull_tens (L M : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isom ((L.pull π hπ).tens (M.pull π hπ)) :=
  isom_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun j y _ => (congrArg₂ (· + ·) (L.φ.pull_φ π hπ _ y) (M.φ.pull_φ π hπ _ y)).trans
      ((L.tens M).φ.pull_φ π hπ j y).symm

theorem isom_pull_ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hu' : ∀ z, CInfAt (fun z => u (ptMap π hπ σ z)) z) :
    ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) hu') :=
  isom_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g (LB.triv X) π (𝟙 Y) x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun j y _ => ((MLine.ofFun u hu).φ.pull_φ π hπ j y).symm

theorem isom_addFn (L : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) :
    (L.addFn u hu).Isom (L.tens (MLine.ofFun u hu)) :=
  isom_of_chart (fun c => (c, PUnit.unit)) (fun _ _ h => ⟨h, trivial⟩)
    (fun x c c' h h' => ((gm_tens L.B (LB.triv X) (𝟙 X) x (c, PUnit.unit) (c', PUnit.unit)
      ⟨h, trivial⟩ ⟨h', trivial⟩).trans ((congrArg (_ * ·) (map_one _)).trans (mul_one _))).symm)
    fun _ _ _ => rfl

theorem isom_pull_pull (L : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) {Z : Scheme.{0}} {r : Z ⟶ Sp k} (i : Z ⟶ Y)
    (hi : i ≫ q = r) (h₀ : (i ≫ π) ≫ p = r) : ((L.pull π hπ).pull i hi).Isom (L.pull (i ≫ π) h₀) :=
  isom_of_chart (fun J => fun _ => J PUnit.unit PUnit.unit)
    (fun _ _ h => mem_pull₂.2 (mem_pull.1 (mem_pull.1 h)))
    (fun x (J J' : PUnit → PUnit → L.B.ι) h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine (gm_pull_g (L.B.pull π) i (𝟙 Z) x J J' h h').trans
        ((gm_pull_g L.B π (𝟙 Z ≫ i) x (J PUnit.unit) (J' PUnit.unit) e e').trans ?_)
      rw [Category.assoc]
      exact (gm_pull_g L.B (i ≫ π) (𝟙 Z) x (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
        (mem_pull₂.2 (mem_pull.1 e)) (mem_pull₂.2 (mem_pull.1 e'))).symm)
    fun (J : PUnit → PUnit → L.B.ι) y _ => by
      refine (L.φ.pull_φ (i ≫ π) h₀ (fun _ => J PUnit.unit PUnit.unit) y).trans (Eq.trans ?_
        ((Weight.pull_φ (L.pull π hπ).φ i hi J y).trans (L.φ.pull_φ π hπ (J PUnit.unit) _)).symm)
      exact congrArg _ (Subtype.ext (by simp [PtsOver.map_val]))

end GlobalTheory.Mix.IsomCalc

open GlobalTheory.Mix.IsomCalc in

theorem GlobalTheory.Mix.isom_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) :=
  fun _ _ _ _ _ _ _ π hπ => ⟨isom_refl, fun _ _ h => isom_pull h π hπ, fun A B => isom_pull_tens A B π hπ,
    fun u hu => isom_pull_ofFun u hu π hπ _, isom_addFn, fun _ _ g hg h A => isom_pull_pull A π hπ g hg h⟩
