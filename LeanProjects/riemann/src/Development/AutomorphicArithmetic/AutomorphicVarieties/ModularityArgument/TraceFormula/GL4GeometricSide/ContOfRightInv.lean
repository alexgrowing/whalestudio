import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CompanionTheory.TwY PositivityTheory.RgBcC.Bridge

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting

private theorem cont_of_right_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_)
  have ho : IsOpen {y : G | g⁻¹ * y ∈ K} := hK.preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ K by simp)] with y hy
  rw [← hf g _ hy, mul_inv_cancel_left]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def Fx (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) : Submodule ℂ π.V where
  carrier := {ψ | ∀ k ∈ K, finRep E n k ψ.1 = ψ.1}
  add_mem' {a b} ha hb k hk := by rw [Submodule.coe_add, map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c a ha k hk := by rw [Submodule.coe_smul, map_smul, ha k hk]

private def res (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (T : Module.End ℂ (Sm E n)) (h1 : T ∈ stabAlg π)
    (h2 : ∀ k, Commute T (finRep E n k)) : Module.End ℂ (Fx π K) :=
  (T.restrict (p := π.V) (q := π.V) h1).restrict fun ψ hψ k hk => by
    change finRep E n k (T ψ.1) = T ψ.1
    rw [← Module.End.mul_apply, ← (h2 k).eq, Module.End.mul_apply, hψ k hk]

private theorem eopW_comm (w : InfinitePlace E) (s : Bool) (a b : Fin n) (k : GL (Fin n) (Af E)) :
    Commute (eopW w s a b) (finRep E n k) := by
  have h : ∀ i j x, Commute (lieS E n i j x) (finRep E n k) := fun i j x => lie_rt_fin _ k
  have h' : ∀ τ : E →+* ℂ, Commute (Eop τ a b) (finRep E n k) := fun τ =>
    ((h a b _).sub_left ((h a b _).smul_left _)).smul_left _
  cases s
  · exact h' _
  · exact h' _

private theorem sV_mem (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) (c : Un n) :
    ∀ ψ ∈ Fx π K, sV π w c ψ ∈ Fx π K := fun ψ hψ k hk => by
  change rt E n (finGL E n k) (rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1) =
    rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]
  exact congrArg _ (hψ k hk)

private def sF (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) :
    Un n →* Module.End ℂ (Fx π K) where
  toFun c := (sV π w c).restrict (sV_mem π K w c)
  map_one' := LinearMap.ext fun ψ => Subtype.ext (by simp)
  map_mul' a b := LinearMap.ext fun ψ => Subtype.ext (by simp)

private theorem along_unit (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (c : Un n) :
    along w g φ c.1 = φ (g * kAt w c) := by
  have e : atW w c.1 = toL (locInf w (Unitary.toUnits c)).val := by
    funext i j v
    exact (locInf_apply w (Unitary.toUnits c) i j v).symm
  rw [along, e, chart_val]
  rfl

private theorem fix_apply {π : CuspSub E n} {K : Subgroup (GL (Fin n) (Af E))} {ψ : π.V} (hψ : ψ ∈ Fx π K)
    {k : GL (Fin n) (Af E)} (hk : k ∈ K) (x : GA E n) : ψ.1.1 (x * finGL E n k) = ψ.1.1 x :=
  (rt_apply (finGL E n k) x ψ.1).symm.trans (congrArg (fun φ : Sm E n => φ.1 x) (hψ k hk))

private theorem thV_mem (π : CuspSub E n) (hθ : ThetaFix π) (K : Subgroup (GL (Fin n) (Af E)))
    (hK : ∀ k ∈ K, thetaF E n k ∈ K) : ∀ ψ ∈ Fx π K, ThInv.thV π hθ ψ ∈ Fx π K := fun ψ hψ k hk =>
  Subtype.ext <| funext fun x => by
    refine (rt_apply (finGL E n k) x _).trans ?_
    rw [ThInv.thV_apply, ThInv.thV_apply, map_mul, ThInv.thetaA_finGL, fix_apply hψ (hK k hk)]

private theorem hecke_ex (hM : HeckeMem) (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E)))
    (ho : IsOpen (K : Set (GL (Fin n) (Af E)))) (hc : IsCompact (K : Set (GL (Fin n) (Af E))))
    [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E)))
    [μf.IsHaarMeasure] (h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}) :
    ∃ R : Module.End ℂ (Fx π K), ∀ u, (R u).1.1.1 = heckeOp μf h.1 u.1.1.1 := by
  have ex : ∀ u : Fx π K, ∃ v : Fx π K, v.1.1.1 = heckeOp μf h.1 u.1.1.1 := fun u => by
    obtain ⟨_, _, ψ', -, h1, h2⟩ := hM E n π K ho hc μf h.1 h.2 u.1
    exact ⟨⟨ψ', h2⟩, h1⟩
  choose r hr using ex
  have hint : ∀ (u : Fx π K) (x : GA E n), Integrable (fun g => h.1 g * u.1.1.1 (x * finGL E n g)) μf := fun u x => by
    refine Continuous.integrable_of_hasCompactSupport (cont_of_right_inv ho fun g k hk => ?_) h.2.1.mul_right
    have e := h.2.2 1 K.one_mem k hk g
    rw [one_mul] at e
    rw [e, map_mul, ← mul_assoc, fix_apply u.2 hk]
  refine ⟨{ toFun := r, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, hr⟩ <;>
    refine Subtype.ext <| Subtype.ext <| Subtype.ext <| funext fun x => ?_
  · change (r (a + b)).1.1.1 x = (r a).1.1.1 x + (r b).1.1.1 x
    rw [hr, hr, hr, heckeOp, heckeOp, heckeOp, ← integral_add (hint a x) (hint b x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_add _ _ _
  · change (r (c • a)).1.1.1 x = c * (r a).1.1.1 x
    rw [hr, hr, heckeOp, heckeOp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_left_comm _ _ _

@[reducible] private def core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hH : IsPet π H) : InnerProductSpace.Core ℂ (Fx π K) where
  inner x y := H x.1 y.1
  conj_inner_symm x y := hH.1 _ _
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx]
    · exact (hH.2.1 _ hx).le
  add_left x y z := by simp
  smul_left x y c := by simp
  definite x hx := by
    by_contra h0
    have := hH.2.1 x.1 fun e => h0 (Subtype.ext e)
    have hx' : H x.1 x.1 = 0 := hx
    simp [hx'] at this

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlEx :
    PetEx → HeckeMem → RlEx := by
  intro hP hM E _ _ _ n hn π hθ K ho hc hK _ _ μf _
  obtain ⟨H, hH⟩ := hP E n hn π hθ
  choose R hR using hecke_ex hM π K ho hc μf
  letI c : InnerProductSpace.Core ℂ (Fx π K) := core π K H hH
  exact ⟨{
    U := Fx π K
    nacg := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    ips := InnerProductSpace.ofCore c.toCore
    i := (Fx π K).subtype
    inj := Subtype.val_injective
    rng := fun ψ => ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨ψ, h⟩, rfl⟩⟩
    H := H
    pet := hH
    inner_eq := fun _ _ => rfl
    E1 := fun w a b => res π K _ (eopW_mem_stabAlg π w true a b) (eopW_comm w true a b)
    E2 := fun w a b => -res π K _ (eopW_mem_stabAlg π w false b a) (eopW_comm w false b a)
    σ := sF π K
    Θ := (ThInv.thV π hθ).restrict (thV_mem π hθ K hK)
    R := R
    hE1 := fun _ _ _ _ => rfl
    hE2 := fun _ _ _ _ => rfl
    hσ := fun w k u g => (rt_apply (kAt w k) g u.1.1).trans (along_unit w g _ k).symm
    hΘ := fun u g => ThInv.thV_apply π hθ u.1 g
    hR := hR }⟩

end
