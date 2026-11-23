import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChgFromBlocksEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceSubmatrixSumMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotStages
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CurveDens

open Matrix
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

set_option maxHeartbeats 2000000 in

theorem bcDens_stage_of_frames {A M B L Q V : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {u : A ⟶ B}
    {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {q₂ : B ⟶ V} {w₀ : f ≫ q₀ = 0} {w₁ : g ≫ q₁ = 0} {w₂ : u ≫ q₂ = 0}
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {l : L ⟶ V} {m : V ⟶ Q} {w₃ : l ≫ m = 0}
    (hS₃ : (ShortComplex.mk l m w₃).ShortExact) {n : ℕ} (hA : IsVB A n) (hM : IsVB M (n + 1))
    (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g)
    {h : Met p σ B (n + 1 + 1)} (hfg : f ≫ g = u) (hlq : q₀ ≫ l = g ≫ q₂) (hmq : q₂ ≫ m = q₁)
    (H : h.IsCInf) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) {U : X.Opens}
    (hyU : y ∈ ptsIn p σ U) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U)) (t₁ : Fin 1 → Γ(B, U))
    (he : IsFrame e) (ht : IsFrame fun i => q₀.app U (t i))
    (ht₁ : IsFrame fun i => q₁.app U (t₁ i)) :
    Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y +
        Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y +
        Met.bcDens (S := ShortComplex.mk l m w₃)
          (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  have hfg' (s : Γ(A, U)) : g.app U (f.app U s) = u.app U s := congr(($hfg).app U s)
  have hlq' (s : Γ(M, U)) : l.app U (q₀.app U s) = q₂.app U (g.app U s) := congr(($hlq).app U s)
  have hmq' (s : Γ(B, U)) : m.app U (q₂.app U s) = q₁.app U s := congr(($hmq).app U s)
  let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
  let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
    ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
  have ht₃ : IsFrame fun i => m.app U (q₂.app U (t₁ i)) := by simpa only [hmq'] using ht₁
  let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 :=
    ⟨U, fun i => q₀.app U (t i), fun i => q₂.app U (t₁ i), ht, ht₃⟩
  let t₂ : Fin (1 + 1) → Γ(B, U) :=
    Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
  have ht₂e (j : Fin 1 ⊕ Fin 1) : q₂.app U (t₂ (finSumFinEquiv j)) = a₃.frame j := by
    rcases j with j | j
    · simp [t₂, a₃, AdaptedChart.frame, hlq']
    · simp [t₂, a₃, AdaptedChart.frame]
  have ht₂ : IsFrame fun i => q₂.app U (t₂ i) := by
    have e₀ : (fun i => q₂.app U (t₂ i)) = (a₃.mid hS₃).e := by
      funext i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      rw [ht₂e]
      simp [AdaptedChart.mid]
    rw [e₀]
    exact (a₃.mid hS₃).isFrame
  let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, ht₂⟩
  let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
    Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
  have hT₀ (x : Fin n ⊕ Fin 1) : g.app U (a₀.frame x) = T (Sum.map id Sum.inl x) := by
    rcases x with i | i
    · simp [a₀, T, AdaptedChart.frame, hfg']
    · simp [a₀, T, AdaptedChart.frame]
  have hT₁ (x : (Fin n ⊕ Fin 1) ⊕ Fin 1) :
      a₁.frame (Sum.map finSumFinEquiv id x) = T (Equiv.sumAssoc _ _ _ x) := by
    rcases x with (i | i) | i
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid, hfg']
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid]
    · simp [a₁, T, AdaptedChart.frame]
  have hT₂ (x : Fin n ⊕ (Fin 1 ⊕ Fin 1)) :
      a₂.frame (Sum.map id finSumFinEquiv x) = T x := by
    rcases x with i | i | i
    · simp [a₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]

  let K : CxPts p σ → Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) ℂ := h.gram T
  have g₀ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (h.restrict hg hM).gram a₀.frame z =
        (K z).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
    ext i j
    refine ((h.form_restrict hg hM _ _ hz).trans ?_)
    rw [hT₀, hT₀]
    rfl
  have g₁ {z : CxPts p σ} : (K z).submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) =
      (h.gram a₁.frame z).submatrix (Sum.map finSumFinEquiv (Equiv.refl (Fin 1)))
        (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₁.frame _) (a₁.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₁ i).symm (hT₁ j).symm
  have g₂ {z : CxPts p σ} : K z =
      (h.gram a₂.frame z).submatrix (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv)
        (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₂.frame _) (a₂.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₂ i).symm (hT₂ j).symm
  have g₃ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram a₃.frame z =
        quotGram (K z) := by
    have e₀ := (QuotStage.quotStages (Fin n) (Fin (1 + 1)) Unit).2 (Fin n) (Fin 1 ⊕ Fin 1)
      (Equiv.refl _) finSumFinEquiv (h.gram a₂.frame z)
    ext i j
    rw [g₂, e₀, submatrix_apply, ← Met.quot_G h hS₂ hA hV a₂ hz,
      ← Met.form_frame _ a₂.quot hz]
    exact congrArg₂ (fun s s' => (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1)
      h hS₂ hA hV).form s s' z) (ht₂e i).symm (ht₂e j).symm
  have hW : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ U :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
      (ChartGlue.mem_over c.e hy hyU)) fun _ hv => hv.2
  have d₀ : Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₀ hA hL a₀ c (H.restrict hg hM) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₀ hv)]
  have d₁ : Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₁ hM hQ a₁ c H hy hyU, Met.bcForm]
    simp only [g₁]
    rw [extTrace_submatrix_sumMap]
  have d₂ : Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y =
      2 * diagVal (extTrace (fun v => K (c.e.symm v)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₂ hA hV a₂ c H hy hyU, Met.bcForm]
    simp only [g₂]
    rw [extTrace_submatrix_sumMap]
  have d₃ : Met.bcDens (S := ShortComplex.mk l m w₃)
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y =
      2 * diagVal (extTrace (fun v => quotGram (K (c.e.symm v))) (c.e y))
        (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₃ hL hQ a₃ c (Met.IsCInf.quot hS₂ hA hV H) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₃ hv)]
  have hK : MContDiffAt 1 (fun v => K (c.e.symm v)) (c.e y) :=
    ((H.gram T hyU).mContDiffAt c hy).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 (c.e y), (K (c.e.symm v)).PosDef := hW.mono fun v hv => by
    rw [g₂]
    exact (Met.posDef_gram_frame (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ a₂ hv).submatrix
      ((Equiv.refl (Fin n)).injective.sumMap finSumFinEquiv.injective)
  have key := congrArg (fun w => (-Complex.I * w).re)
    (extTrace_add_extTrace (ReciprocityTheory.L2DbarEstimates.V 1) (Fin n) (Fin 1) (Fin 1) (fun v => K (c.e.symm v))
      (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) hK hp)
  simp only [mul_add, Complex.add_re] at key
  rw [d₀, d₁, d₂, d₃]
  simp only [diagVal]
  linarith

theorem bcDens_add_bcDens_stage : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  intro k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h
    hfg hlq hmq H c y hy
  obtain ⟨b₀, hb₀⟩ := Met.exists_adapted (p := p) (σ := σ) hS₀ hA hL y
  obtain ⟨b₁, hb₁⟩ := Met.exists_adapted hS₁ hM hQ y
  refine bcDens_stage_of_frames hS₀ hS₁ hS₂ hS₃ hA hM hL hQ hV hg hfg hlq hmq H c hy
    (U := b₀.U ⊓ b₁.U) (mem_ptsIn_inf.2 ⟨hb₀, hb₁⟩) (fun i => resM A inf_le_left (b₀.e i))
    (fun i => resM M inf_le_left (b₀.t i)) (fun i => resM B inf_le_right (b₁.t i))
    (b₀.he.res inf_le_left) ?_ ?_
  · simp only [app_resM]
    exact b₀.ht.res inf_le_left
  · simp only [app_resM]
    exact b₁.ht.res inf_le_right

end GlobalTheory.CurveDens
