import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem np_desc_sep {K : Type} [Field K] (a : PowerSeries K)
    (h : ∀ m : ℕ, a ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ m) : a = 0 := by
  ext i
  have := h (i + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  simpa using this i (Nat.lt_succ_self i)

theorem UpperTheory.V.Pa.np_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (x : NP G.frame n) (k : Kap x) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → x.UnipOn H → g.p.ker = PL l H → (∃ ρ' : G'.G₀ →* GL (Fin n) x.A, ∀ a, ρ' (g.p₀ a) = x.ρ a) ∧ ∃ κ' : Fin k.g → G'.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ j a, κ' j (g.p₀ a) = k.κ j a := by
  intro l _ L G G' g n x k H _ hH hη hU hker
  have hρ : ∀ d, x.ρX x.A d = mat x.ρ d := by
    intro d
    ext i j
    simp [NP.ρX]
  obtain ⟨hR, -, -, -⟩ := rho_hom l G.frame n x k x.A
  have hl : (l : x.A) = 0 := by
    have := (am_fin l G.frame n x 0 0).2.2.2.2.1
    simpa using this
  have hunip : ∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e, ∀ i j,
      (x.ρX x.A (h ^ l ^ e) - 1) i j ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m := by
    intro m h hh
    obtain ⟨e, he⟩ := hU m h hh
    refine ⟨e, fun i j => ?_⟩
    rw [hρ, show algebraMap x.A x.A x.t = x.t from rfl, Ideal.span_singleton_pow]
    exact he i j
  have sep : ∀ a : x.A, (∀ m, a ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m) → a = 0 :=
    fun a h => np_desc_sep a h
  have key : ∀ d : G.G₀, g.p₀ d = 1 → x.ρ d = 1 ∧ ∀ j, k.κ j d = 0 := by
    intro d hd
    have hdP : (d : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, hd]
      rfl
    constructor
    · have h0 := (coc_pl l L G n x.A _ (x.ρX x.A) (fun _ => 0) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (fun i j N => IsLocallyConstant.const _) (fun a b => by simp)).2 d hdP
      apply Units.ext
      have hm : x.ρX x.A d = 1 :=
        Matrix.ext fun i j => sub_eq_zero.mp (sep _ (fun m => (h0 m i j).1))
      rw [hρ] at hm
      exact hm
    · intro j
      have hj := (coc_pl l L G n x.A _ (x.ρX x.A) (k.κ j) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (k.mem j).2.1 (k.mem j).2.2.1).2 d hdP
      exact Matrix.ext fun a b => sep _ (fun m => (hj m a b).2)
  have hkerρ : g.p₀.ker ≤ x.ρ.ker := fun d hd => (key d hd).1
  let e := QuotientGroup.quotientKerEquivOfSurjective g.p₀ g.p₀_surj
  refine ⟨⟨(QuotientGroup.lift g.p₀.ker x.ρ hkerρ).comp e.symm.toMonoidHom, fun a => ?_⟩,
    ⟨fun j b => k.κ j (Classical.choose (g.p₀_surj b)), fun j a => ?_⟩⟩
  · have hs : e.symm (g.p₀ a) = (QuotientGroup.mk a : G.G₀ ⧸ g.p₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift g.p₀.ker x.ρ hkerρ (e.symm (g.p₀ a)) = x.ρ a
    rw [hs]
    rfl
  · have hc : g.p₀ (Classical.choose (g.p₀_surj (g.p₀ a))) = g.p₀ a :=
      Classical.choose_spec (g.p₀_surj (g.p₀ a))
    set c := Classical.choose (g.p₀_surj (g.p₀ a))
    have hd : g.p₀ (c⁻¹ * a) = 1 := by rw [map_mul, map_inv, hc, inv_mul_cancel]
    have h3 := (k.mem j).2.2.1 c (c⁻¹ * a)
    rw [mul_inv_cancel_left, (key _ hd).2 j] at h3
    simp at h3
    exact h3.symm
