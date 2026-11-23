import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini :
    Euler → Fub → SideAbs := by
  intro hE hF V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K
    T _ _ _ _ _ _ _ _ Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hRP hRPT j ji jv
    hqj hpj hK μ μi m ν νi nv hP hPi hPv S a b ha hb hEa hEb θ θi θv hqθ hpθ cθi cθv
    δ z cz hpz hinv hC hB φi φ cφi sφi cφ hS
  classical
  have invI : ∀ t, (ji t)⁻¹ * q δ * θi (ji t) = q δ := by
    intro t
    obtain ⟨τ, h1, -⟩ := hRPT.surj t (fun _ => 1) (Filter.Eventually.of_forall fun v => one_mem _)
    have h := congrArg q (hinv τ)
    rw [map_mul, map_mul, map_inv, hqθ, hqj, h1] at h
    exact h
  have invV : ∀ v t, (jv v t)⁻¹ * p v δ * θv v (jv v t) = p v δ := by
    intro v t
    have hev : ∀ᶠ w in Filter.cofinite, Function.update (fun w => (1 : Tv w)) v t w ∈ KT w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
      exact one_mem _
    obtain ⟨τ, -, h1⟩ := hRPT.surj 1 _ hev
    have h2 : pT v τ = t := by rw [h1 v, Function.update_self]
    have h := congrArg (p v) (hinv τ)
    rw [map_mul, map_mul, map_inv, hpθ, hpj, h2] at h
    exact h
  have twI : ∀ t g, (ji t * g)⁻¹ * q δ * θi (ji t * g) = g⁻¹ * q δ * θi g := by
    intro t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (ji t)⁻¹ * q δ * (θi (ji t) * θi g)
        = g⁻¹ * ((ji t)⁻¹ * q δ * θi (ji t)) * θi g := by simp only [mul_assoc]
      _ = g⁻¹ * q δ * θi g := by rw [invI]
  have twV : ∀ v t g, (jv v t * g)⁻¹ * p v δ * θv v (jv v t * g) = g⁻¹ * p v δ * θv v g := by
    intro v t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (jv v t)⁻¹ * p v δ * (θv v (jv v t) * θv v g)
        = g⁻¹ * ((jv v t)⁻¹ * p v δ * θv v (jv v t)) * θv v g := by simp only [mul_assoc]
      _ = g⁻¹ * p v δ * θv v g := by rw [invV]
  let Fi : Gi → ℂ := fun x => ∫ s, φi (q (z s) * (x⁻¹ * q δ * θi x))
  let Fv : ∀ v, Gv v → ℂ := fun v x => φ v (x⁻¹ * p v δ * θv v x)
  have hf := hF Gi Ti μi ji νi hPi θi (q δ) (fun s => q (z s)) cθi (hRP.cq.comp cz) invI hC hB
    φi cφi sφi
  have hfm : Measurable Fi := hf.1
  have hf2 : qI μi ji νi Fi = ∫ s, qI μi ji νi fun x => φi (q (z s) * (x⁻¹ * q δ * θi x)) := hf.2
  have hFiI : ∀ t g, Fi (ji t * g) = Fi g := by
    intro t g
    show (∫ s, φi (q (z s) * ((ji t * g)⁻¹ * q δ * θi (ji t * g)))) = ∫ s, φi (q (z s) * (g⁻¹ * q δ * θi g))
    simp only [twI]
  have hFv : ∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g := by
    intro v
    refine ⟨((cφ v).comp ((continuous_inv.mul continuous_const).mul (cθv v))).measurable, ?_⟩
    intro t g
    show φ v ((jv v t * g)⁻¹ * p v δ * θv v (jv v t * g)) = φ v (g⁻¹ * p v δ * θv v g)
    rw [twV]
  have hFS : ∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧
      ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0) := by
    intro v hv x
    obtain ⟨h1, h2⟩ := hS v hv
    constructor
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 1
      rw [h1]
      exact Set.indicator_of_mem ((h2 x).2 h) _
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 0
      rw [h1]
      exact Set.indicator_of_notMem (fun hm => h ((h2 x).1 hm)) _
  have he := hE V G Gi Gv q p K T Ti Tv qT pT KT hRP hRPT j ji jv hqj hpj hK μ μi m ν νi nv
    hP hPi hPv S a b ha hb hEa hEb Fi Fv hfm hFiI hFv hFS
  have key : (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) *
      ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) = fun x => Fi (q x) * ∏ᶠ v, Fv v (p v x) := by
    funext x
    have h1 : ∀ s, q (z s * (x⁻¹ * δ * θ x)) = q (z s) * ((q x)⁻¹ * q δ * θi (q x)) := by
      intro s
      rw [map_mul, map_mul, map_mul, map_inv, hqθ]
    have h2 : ∀ s v, p v (z s * (x⁻¹ * δ * θ x)) = (p v x)⁻¹ * p v δ * θv v (p v x) := by
      intro s v
      rw [map_mul, hpz, one_mul, map_mul, map_mul, map_inv, hpθ]
    simp only [h1, h2]
    exact integral_mul_const _ _
  rw [key]
  exact ⟨he.1, he.2.trans (congrArg (fun w => ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * w *
    ∏ v ∈ S, qI (m v) (jv v) (nv v) (Fv v)) hf2)⟩
