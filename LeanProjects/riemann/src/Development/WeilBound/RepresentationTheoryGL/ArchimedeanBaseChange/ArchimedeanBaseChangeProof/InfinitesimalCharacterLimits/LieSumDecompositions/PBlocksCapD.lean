import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapC

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem decomp_G (G : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hcap : ∀ τ u, cap τ u G = ((mm τ).map (u + ·)).prod • G)
    {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) (hb : ∀ i, IsAutForm (b i)) (hq : ∀ i, IsAutForm (q i))
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) :
    ∃ (S : Finset ((E →+* ℂ) → Multiset ℂ)) (x : ((E →+* ℂ) → Multiset ℂ) → (GA E r × GA E s → ℂ)),
      (∀ p, G.1 (lev (Ad E) r s p) = ∑ σ ∈ S, x σ p) ∧
      ∀ σ ∈ S, (∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = r) ∧
        (∀ m₂, ∃ θ ∈ zspan b, (∀ y, x σ (y, m₂) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((σ τ).map (fun z => w + (s : ℂ) / 2 + z)).prod • θ) ∧
        (∀ m₁, ∃ θ ∈ zspan q, (∀ y, x σ (m₁, y) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((mm τ - σ τ).map (fun z => w - (r : ℂ) / 2 + z)).prod • θ) := by
  classical
  have := zspan_fd b hb
  have := zspan_fd q hq
  have := fd_tens2 (zspan b) (zspan q)
  have ca := fun τ : E →+* ℂ => cap_coeff (E := E) r τ (-(s : ℂ) / 2)
  choose fa ha1 haZ haeq using ca
  have cb := fun τ : E →+* ℂ => cap_coeff (E := E) s τ ((r : ℂ) / 2)
  choose fb hb1 hbZ hbeq using cb
  let AA : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp (fa τ j) LinearMap.id
  let BB : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp LinearMap.id (fb τ j)
  let v : GA E r × GA E s → ℂ := fun p => ∑ i, (b i).1 p.1 * (q i).1 p.2
  have hAW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => zspan_stable b (haZ τ j) _ (h₁ i)) (fun i => h₂ i)
  have hBW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => h₁ i) (fun i => zspan_stable q (hbZ τ j) _ (h₂ i))
  have hAA : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (AA τ' l w) = AA τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp (fa τ' l) LinearMap.id _) =
      tensOp (fa τ' l) LinearMap.id (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, (GlobalTheory.LeviGL.ZGood.zalg_commute (haZ τ j) (haZ τ' l)).eq, Module.End.mul_apply]
  have hAB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (BB τ' l w) = BB τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    rfl
  have hBB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j (BB τ' l w) = BB τ' l (BB τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp LinearMap.id (fb τ j) _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply (fb τ j), (GlobalTheory.LeviGL.ZGood.zalg_commute (hbZ τ j) (hbZ τ' l)).eq, Module.End.mul_apply]
  have hA1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ r w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ r) LinearMap.id _ = _
    rw [tensOp_sum, ha1 τ]
    rfl
  have hB1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ s w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ s) _ = _
    rw [tensOp_sum, hb1 τ]
    rfl
  have hv : v ∈ tens2 (zspan b) (zspan q) := A.sum_mem (fun i => mem_zspan b i) (fun i => mem_zspan q i)
  have hrel : ∀ τ (u : ℂ), (∑ j ∈ Finset.range (r + 1), u ^ j • AA τ j) ((∑ l ∈ Finset.range (s + 1), u ^ l • BB τ l) v) =
      ((mm τ).map (u + ·)).prod • v := by
    intro τ u
    change (∑ j ∈ Finset.range (r + 1), u ^ j • tensOp (fa τ j) LinearMap.id)
      ((∑ l ∈ Finset.range (s + 1), u ^ l • tensOp LinearMap.id (fb τ l)) v) = _
    rw [tensR_apply, ← hbeq τ u, tensL_apply, ← haeq τ u]
    funext p
    have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
    rw [e, rel_expand G hu τ (fun u => ((mm τ).map (u + ·)).prod) (hcap τ) b q hG u p]
    rfl
  obtain ⟨S, x, hxW, hsum, hprop⟩ := BlockAlgebra.decomp r s AA BB mm (tens2 (zspan b) (zspan q)) hAW hBW hAA hAB hBB
    hA1 hB1 hmm v hv hrel
  refine ⟨S, x, fun p => ?_, fun σ hσ => ⟨fun τ => ⟨(hprop σ hσ τ).1, (hprop σ hσ τ).2.1⟩, fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · rw [hG]
    change v p = _
    rw [hsum, Finset.sum_apply]
  · obtain ⟨n, ψ₁, ψ₂, h₁, -, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₂ i).1 m₂ • ψ₁ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i),
      fun y => by rw [hx]; simp [Finset.sum_apply, mul_comm], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w + (s : ℂ) / 2)).1
    change (∑ j ∈ Finset.range (r + 1), (w + (s : ℂ) / 2) ^ j • tensOp (fa τ j) LinearMap.id) (x σ) = _ at key
    rw [hx, tensL_apply, ← haeq τ] at key
    have e : w + (s : ℂ) / 2 + -(s : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (y, m₂)
    simp only [Pi.smul_apply, smul_eq_mul] at k2
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    simp only [mul_comm ((ψ₂ _).1 m₂)] at k2 ⊢
    rw [k2, Finset.mul_sum]
  · obtain ⟨n, ψ₁, ψ₂, -, h₂, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₁ i).1 m₁ • ψ₂ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i),
      fun y => by rw [hx]; simp [Finset.sum_apply], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w - (r : ℂ) / 2)).2
    change (∑ j ∈ Finset.range (s + 1), (w - (r : ℂ) / 2) ^ j • tensOp LinearMap.id (fb τ j)) (x σ) = _ at key
    rw [hx, tensR_apply, ← hbeq τ] at key
    have e : w - (r : ℂ) / 2 + (r : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (m₁, y)
    simp only [Pi.smul_apply, smul_eq_mul] at k2
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [k2, Finset.mul_sum]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
