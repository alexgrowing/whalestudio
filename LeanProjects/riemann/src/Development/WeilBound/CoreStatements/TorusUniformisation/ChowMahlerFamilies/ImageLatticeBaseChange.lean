import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XGraphRestrictBc

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.ImageLatticeBaseChange

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem isBaseChange_bcMap (C : Type) [Field C] [Algebra Ω C] (m : ℕ) :
    IsBaseChange C (bcMap Ω C (Fin m)) :=
  IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap Ω C)

theorem locFree_div (R : Subalgebra o Ω) {m : ℕ} {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup (Fin m → Ω)) (hL : ∀ v, v ∈ L ↔ ∀ i, w * v i ∈ R) : LocFree R m L := by
  have hb : ∀ a : Fin m → Ω, (∑ q, a q • w⁻¹ • (Pi.single q 1 : Fin m → Ω)) = fun i => a i * w⁻¹ := by
    intro a
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp,
    fun _ => ⟨fun q => w⁻¹ • (Pi.single q 1 : Fin m → Ω), ?_, ?_, ?_⟩⟩
  · intro a ha e he
    rw [hL] at he ⊢
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    exact R.mul_mem ha (he i)
  · have h := (Pi.basisFun Ω (Fin m)).linearIndependent.map'
      (LinearEquiv.smulOfNeZero Ω (Fin m → Ω) w⁻¹ (inv_ne_zero hw)).toLinearMap
      (LinearEquiv.ker _)
    simpa [Function.comp_def] using h
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ q, (w * x q) • (w⁻¹ • (Pi.single q 1 : Fin m → Ω)) := by
      rw [hb (fun q => w * x q)]
      funext i
      field_simp
    rw [hx]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · intro e
    constructor
    · rintro ⟨k, hk⟩
      simp only [one_pow, one_smul] at hk
      refine ⟨fun q => w * e q, fun q => ⟨0, by simpa using (hL e).1 hk q⟩, ?_⟩
      rw [hb]
      funext i
      field_simp
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      simp only [pow_zero, one_smul]
      rw [hb, hL]
      intro i
      obtain ⟨k, hk⟩ := ha i
      simp only [one_pow, one_mul] at hk
      field_simp
      exact hk

end PositivityTheory.Xgn.ImageLatticeBaseChange

private theorem dotDual_spanOver_bcMap_eq {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {m k : ℕ} (A : AddSubgroup (Fin m → Ω)) (a γ : Fin k → Fin m → Ω) (ha : ∀ i, a i ∈ A)
    (hγ : ∀ i, γ i ∈ dotDual R A) (hid : ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0) :
    dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' A)) = spanOver RC (bcMap Ω C (Fin m) '' dotDual R A) := by
  have hb : ∀ (v : Fin m → Ω) j, bcMap Ω C (Fin m) v j = algebraMap Ω C (v j) := fun _ _ => rfl
  have hdot : ∀ u v : Fin m → Ω,
      bcMap Ω C (Fin m) u ⬝ᵥ bcMap Ω C (Fin m) v = algebraMap Ω C (u ⬝ᵥ v) := by
    intro u v
    simp only [dotProduct, hb, map_sum, map_mul]
  apply le_antisymm
  · intro y hy
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hy
    have hy' : y = ∑ i, (bcMap Ω C (Fin m) (a i) ⬝ᵥ y) • bcMap Ω C (Fin m) (γ i) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, hb]
      calc y j = ∑ l, y l * algebraMap Ω C (if l = j then 1 else 0) := by
            simp [apply_ite]
        _ = ∑ i, (∑ l, algebraMap Ω C (a i l) * y l) * algebraMap Ω C (γ i j) := by
            simp_rw [← hid, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
            ring
    rw [hy']
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hy _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a i, ha i, rfl⟩, (one_smul _ _).symm⟩),
        _, ⟨γ i, hγ i, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨g, hg, rfl⟩, rfl⟩
    have hg' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R A g).1 hg
    rw [SetLike.mem_coe, PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩ := hv
      rw [smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hd (RC.mul_mem hc (hR _ (hg' u hu)))
    | zero => simp
    | add u v _ _ hu hv =>
      rw [add_dotProduct]
      exact add_mem hu hv
    | neg u _ hu =>
      rw [neg_dotProduct]
      exact neg_mem hu

private theorem exists_dual_pair_af_of_summand_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) (hS : Summand (D.l1 R p) (linMap n χ).range)
    (hl1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)) :
    ∃ (k : ℕ) (a γ : Fin k → Fin n → Ω), (∀ i, a i ∈ D.af R p χ) ∧ (∀ i, γ i ∈ dotDual R (D.af R p χ)) ∧
      ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0 := by
  classical
  obtain ⟨π, hπ, hπL⟩ := PositivityTheory.Xgn.GoodLatticeBaseChange.af_retract R D p χ h0 h1 hS
  let L1 : Submodule R ((Fin n → F) → Ω) :=
    { carrier := D.l1 R p
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c v hv => hl1.1 c c.2 v hv }
  obtain ⟨k, φ, u, hφ, hsum⟩ := GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.exists_dualBasis (L := L1) hl1
  refine ⟨k * Fintype.card F ^ n, fun i => π (u (finProdFinEquiv.symm i)),
    fun i j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1)), ?_, ?_, ?_⟩
  · intro i
    exact hπL _ (u _).2
  · intro i
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    have hv' : v = ∑ j, v j • (Pi.single j 1 : Fin n → Ω) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    have hval : v ⬝ᵥ (fun j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1))) =
        φ (finProdFinEquiv.symm i) (linMap n χ v) := by
      conv_rhs => rw [hv']
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
    rw [hval]
    exact hφ _ _ hv
  · intro l j
    have h := congrArg (fun e => π e l) (hsum (linMap n χ (Pi.single j 1)))
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at h
    rw [show (if l = j then (1 : Ω) else 0) = (Pi.single j 1 : Fin n → Ω) l by simp [Pi.single_apply], ← h]
    exact (finProdFinEquiv.symm.sum_comp
      (fun x => π (u x) l * φ x (linMap n χ (Pi.single j 1)))).trans
      (Finset.sum_congr rfl fun x _ => mul_comm _ _)

private theorem map_snd_spanOver_prodMap_eq {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    {X Y Xc Yc : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Xc] [Module C Xc] [AddCommGroup Yc]
    [Module C Yc] (f : X → Xc) (g : Y → Yc) (S : AddSubgroup (X × Y)) :
    AddSubgroup.map (AddMonoidHom.snd Xc Yc) (spanOver RC (Prod.map f g '' S)) =
      spanOver RC (g '' AddSubgroup.map (AddMonoidHom.snd X Y) S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, g x.2, ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • Prod.map f g x, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

open PositivityTheory.Xgn.ImageLatticeBaseChange PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.image_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG hw C _ _ _ _ RC hR τ
  obtain ⟨hp, hwR, ⟨c, hc, hpc⟩, h01, hχ⟩ := hC
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hp
    rw [hpc, mul_zero]
  obtain ⟨hχ0, hχ1, hχR⟩ := hχ τ
  obtain ⟨k, a, γ, ha, hγ, hid⟩ := exists_dual_pair_af_of_summand_locFree D R p (χ τ) hχ0 hχ1 (hG.lin τ) hG.l1
  have hhh : (D.bc RC).hh RC p (fun x => algebraMap Ω C (χ τ x)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) := by
    unfold LieLatticeData.hh
    rw [PositivityTheory.Xgn.GoodLatticeBaseChange.af_bc R RC D p hR (χ τ) hχ0 hχ1 (hG.lin τ)]
    exact dotDual_spanOver_bcMap_eq R RC hR (D.af R p (χ τ)) a γ ha hγ hid
  have hstab : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hB.stable τ a ha).2.1
  have hfst : ∀ v, v ∈ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) ↔ ∀ i, w * v i ∈ R := by
    intro v
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b, c'⟩, hbc, rfl⟩
      have := ((hB.del τ).1 b).1 ⟨c', hbc⟩
      rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat] at this
      exact this
    · intro hv
      obtain ⟨c', hc'⟩ := ((hB.del τ).1 v).2 ((PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 hv)
      exact ⟨(v, c'), hc', rfl⟩
  have hLF := PositivityTheory.Xgn.ImageLatticeBaseChange.locFree_div R hw0 _ hfst
  have hHle : D.hh R p (χ τ) ≤ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) := by
    intro v hv
    rw [hfst]
    intro i
    have hv' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R _ v).1 hv
    have hmem : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p (χ τ) :=
      hw τ ⟨Pi.single i 1, (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 (fun j => by
        by_cases h : j = i <;> simp [h, Pi.single_apply, R.one_mem, R.zero_mem]), rfl⟩
    have := hv' _ hmem
    simpa [smul_dotProduct, single_dotProduct] using this
  have hHst : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    unfold LieLatticeData.hh at hv ⊢
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hv ⊢
    intro u hu
    rw [dotProduct_smul, smul_eq_mul]
    exact R.mul_mem ha (hv u hu)
  have hg := (PositivityTheory.Xgn.t_graph_restrict_bc R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C n) (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C (s τ))
    (D.Del τ) (D.hh R p (χ τ)) n hstab hLF hHle hHst).1
  unfold LieLatticeData.imH
  rw [hhh]
  change AddSubgroup.map _ (spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' ↑(D.Del τ)) ⊓ _) = _
  rw [hg]
  exact map_snd_spanOver_prodMap_eq RC _ _ _
