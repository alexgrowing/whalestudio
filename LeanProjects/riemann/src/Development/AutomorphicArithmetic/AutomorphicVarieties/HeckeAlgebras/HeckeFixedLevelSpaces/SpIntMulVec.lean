import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq

open IsLocalRing Matrix UpperTheory.V.Hi

namespace UpperTheory.V.Hi.Sp

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω)

theorem sum_comm {κ : Type} [Fintype κ] (u : κ → X.Ub) (b : Gp) :
    Commute (X.rpF Ω (W.d + 1) m b) (∑ q, X.raF (W.d + 1) τ (u q)) :=
  Commute.sum_right _ _ _ fun q _ => LinearMap.ext fun F => ((ctrlEq Γ Ga Gp X O Ω W m τ).2.2 (u q) b F).symm

private theorem raF_mem_pi_AF_inf_eig (φ : X.I.T →* Ωˣ) (c : ℕ) (u : X.Ub) (F : Fin m → X.Fn Ω (W.d + 1))
    (hF : F ∈ (Submodule.pi Set.univ fun _ => X.AF W.ξ) ⊓ X.I.eig (X.rpF Ω (W.d + 1) m) c φ) :
    X.raF (W.d + 1) τ u F ∈ (Submodule.pi Set.univ fun _ => X.AF W.ξ) ⊓ X.I.eig (X.rpF Ω (W.d + 1) m) c φ := by
  obtain ⟨hA, hN, hNm, hT⟩ := hF
  have hc := (ctrlEq Γ Ga Gp X O Ω W m τ).2.2 u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i _ γ g
    funext k
    show ((τ u).val *ᵥ fun j => F j (X.glob γ * g * ((u : Ga), 1)) k) i =
      ((W.ξ (X.glob γ).2).val *ᵥ (fun l => ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1)) l) i)) k
    have e1 : ∀ j, F j (X.glob γ * g * ((u : Ga), 1)) = (W.ξ (X.glob γ).2).val *ᵥ F j (g * ((u : Ga), 1)) := by
      intro j
      rw [mul_assoc]
      exact hA j (Set.mem_univ j) γ _
    simp only [e1, mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · intro x hx
    rw [← hc, hN x hx]
  · intro y hy
    rw [← hc, hNm y hy]
  · intro t
    rw [← hc, hT t, LinearMap.map_smul]

theorem sum_cl (φ : X.I.T →* Ωˣ) (c : ℕ) (U U' : Subgroup X.Ub) {κ : Type} [Fintype κ] (u : κ → X.Ub) (F)
    (hF : F ∈ X.Cl τ W.ξ U c φ) (h : (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ fixd (X.raF (W.d + 1) τ) U') :
    (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ X.Cl τ W.ξ U' c φ := by
  have hS : ∀ G ∈ (Submodule.pi Set.univ fun _ => X.AF W.ξ) ⊓ X.I.eig (X.rpF Ω (W.d + 1) m) c φ,
      (∑ q, X.raF (W.d + 1) τ (u q)) G ∈
        (Submodule.pi Set.univ fun _ => X.AF W.ξ) ⊓ X.I.eig (X.rpF Ω (W.d + 1) m) c φ := by
    intro G hG
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun q _ => raF_mem_pi_AF_inf_eig X W τ φ c (u q) G hG
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  obtain ⟨h4, h5⟩ := hS F ⟨h1, h3⟩
  exact ⟨⟨h4, h⟩, h5⟩

private theorem UF_commute_sum_raF {κ : Type} [Fintype κ] (u : κ → X.Ub) (a : X.I.P) :
    Commute (X.UF m W a) (∑ q, X.raF (W.d + 1) τ (u q)) := by
  unfold Frame.UF Iwa.uOp
  refine Commute.smul_left ?_ _
  by_cases hfin : (Function.support fun q : X.I.N ⧸ (X.I.Nconj (a : Gp)).subgroupOf X.I.N =>
      X.rpF Ω (W.d + 1) m (↑(Quotient.out q) * (a : Gp))).Finite
  · rw [finsum_eq_sum _ hfin]
    exact Commute.sum_left _ _ _ fun q _ => UpperTheory.V.Hi.Sp.sum_comm X W τ u _
  · rw [finsum_of_infinite_support hfin]
    exact Commute.zero_left _

theorem sum_clOrd (φ : X.I.T →* Ωˣ) (c : ℕ) (U U' : Subgroup X.Ub) {κ : Type} [Fintype κ] (u : κ → X.Ub)
    (h : ∀ F ∈ fixd (X.raF (W.d + 1) τ) U, (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ fixd (X.raF (W.d + 1) τ) U') (F)
    (hF : F ∈ X.ClOrd W τ U c φ) : (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ X.ClOrd W τ U' c φ := by
  have hcomm := UF_commute_sum_raF X W τ u ⟨X.I.z, X.I.z_mem⟩
  refine Submodule.iSup_induction _ (motive := fun G => (∑ q, X.raF (W.d + 1) τ (u q)) G ∈ X.ClOrd W τ U' c φ)
    hF ?_ ?_ ?_
  · intro μ G hG
    obtain ⟨hG1, hG2⟩ := hG
    refine Submodule.mem_iSup_of_mem μ ⟨?_, ?_⟩
    · exact sum_cl X W τ φ c U U' u G hG1 (h G hG1.1.2)
    · exact Module.End.mapsTo_maxGenEigenspace_of_comm hcomm _ hG2
  · simp only [map_zero]
    exact zero_mem _
  · intro x y hx hy
    simp only [map_add]
    exact add_mem hx hy

private theorem UF_z_comm_and_preserves_N_fixed (a : X.I.P) (G : Fin m → X.Fn Ω (W.d + 1))
    (hG : G ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N) :
    X.UF m W ⟨X.I.z, X.I.z_mem⟩ (X.UF m W a G) = X.UF m W a (X.UF m W ⟨X.I.z, X.I.z_mem⟩ G) ∧
    X.UF m W ⟨X.I.z, X.I.z_mem⟩ G ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N := by
  have hz := uOpMul Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z a X.I.z_mem a.2 G hG
  have ha := uOpMul Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) a X.I.z a.2 X.I.z_mem G hG
  have hza : X.I.z * (a : Gp) = a * X.I.z := X.I.comm _ (X.I.P_le _ X.I.z_mem) _ (X.I.P_le _ a.2)
  unfold Frame.UF
  simp only [LinearMap.smul_apply, LinearMap.map_smul]
  refine ⟨?_, ?_⟩
  · rw [hz.2.1, ha.2.1, hza]
    exact smul_comm _ _ _
  · exact Submodule.smul_mem _ _ hz.1

theorem uf_clOrd (φ : X.I.T →* Ωˣ) (c : ℕ) (U : Subgroup X.Ub)
    (h : ∀ a : X.I.P, ∀ F ∈ X.Cl τ W.ξ U c φ, X.UF m W a F ∈ X.Cl τ W.ξ U c φ) (a : X.I.P) (F)
    (hF : F ∈ X.ClOrd W τ U c φ) : X.UF m W a F ∈ X.ClOrd W τ U c φ := by
  refine Submodule.iSup_induction _ (motive := fun G => X.UF m W a G ∈ X.ClOrd W τ U c φ) hF ?_ ?_ ?_
  · intro μ G hG
    obtain ⟨hG1, hG2⟩ := hG
    have hN : G ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N := hG1.2.1
    refine Submodule.mem_iSup_of_mem μ ⟨h a G hG1, ?_⟩
    simp only [SetLike.mem_coe] at hG2 ⊢
    rw [Module.End.mem_maxGenEigenspace] at hG2 ⊢
    obtain ⟨k, hk⟩ := hG2
    refine ⟨k, ?_⟩
    have key : ∀ n : ℕ, ∀ y ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N,
        ((X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) ^ n) (X.UF m W a y) =
          X.UF m W a (((X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) ^ n) y) ∧
        ((X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) ^ n) y ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N := by
      intro n
      induction n with
      | zero =>
        intro y hy
        rw [pow_zero, Module.End.one_apply, Module.End.one_apply]
        exact ⟨rfl, hy⟩
      | succ n ih =>
        intro y hy
        obtain ⟨ih1, ih2⟩ := ih y hy
        obtain ⟨c1, c2⟩ := UF_z_comm_and_preserves_N_fixed X W a _ ih2
        rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih1]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        refine ⟨?_, ?_⟩
        · rw [c1, map_sub, map_smul]
        · exact sub_mem c2 (Submodule.smul_mem _ _ ih2)
    rw [(key k G hN).1, hk, map_zero]
  · simp only [map_zero]
    exact zero_mem _
  · intro x y hx hy
    simp only [map_add]
    exact add_mem hx hy

theorem clOrd_mono (φ : X.I.T →* Ωˣ) {c c' : ℕ} (hc : c ≤ c') {U U' : Subgroup X.Ub} (hU : U' ≤ U) :
    X.ClOrd W τ U c φ ≤ X.ClOrd W τ U' c' φ :=
  iSup_mono fun _ _ hF => ⟨⟨⟨hF.1.1.1, fun u hu => hF.1.1.2 u (hU hu)⟩, hF.1.2.1,
    fun y hy => hF.1.2.2.1 y (X.I.Nm_anti hc hy), hF.1.2.2.2⟩, hF.2⟩

end UpperTheory.V.Hi.Sp
