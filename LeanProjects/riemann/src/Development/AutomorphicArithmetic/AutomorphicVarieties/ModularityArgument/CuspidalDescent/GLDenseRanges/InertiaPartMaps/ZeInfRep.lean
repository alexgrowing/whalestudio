import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.LinkedUnitaryEndsOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M] {J : Type} [Fintype J]

private theorem ze_zero (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (x : J → M) (hx : ∀ i, x i ∈ Y i)
    (h : ∑ i, x i = 0) (i : J) : x i = 0 := by
  classical
  have h1 : x i = - ∑ j ∈ Finset.univ.erase i, x j := by
    rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact h
  have h2 : x i ∈ ⨆ (j) (_ : j ≠ i), Y j := by
    rw [h1]
    refine neg_mem (sum_mem fun j hj => ?_)
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hj) (hx j))
  exact Submodule.disjoint_def.1 (hY i) _ (hx i) h2

private theorem ze_dec (D : J → Submodule ℂ M) {F : M} (h : F ∈ ⨆ i, D i) :
    ∃ x : J → M, (∀ i, x i ∈ D i) ∧ ∑ i, x i = F := by
  classical
  induction h using Submodule.iSup_induction' with
  | mem i y hy =>
    refine ⟨Pi.single i y, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact hy
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    · rw [Finset.sum_eq_single i (fun j _ hj => Pi.single_eq_of_ne hj _) (fun h => absurd (Finset.mem_univ i) h),
        Pi.single_eq_same]
  | zero => exact ⟨0, fun _ => zero_mem _, Finset.sum_const_zero⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), Finset.sum_add_distrib⟩

private theorem ze_rank (E : J → Submodule ℂ M) (hE : iSupIndep E) (Z : Submodule ℂ M) [FiniteDimensional ℂ Z]
    (hZ : ∀ i, E i ≤ Z) : Module.finrank ℂ ↥(⨆ i, E i) = ∑ i, Module.finrank ℂ ↥(E i) := by
  classical
  have key : ∀ s : Finset J, Module.finrank ℂ ↥(⨆ i ∈ s, E i) = ∑ i ∈ s, Module.finrank ℂ ↥(E i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset J), E i) = ⊥ :=
        le_bot_iff.1 (iSup₂_le fun i hi => absurd hi (Finset.notMem_empty i))
      rw [h0, finrank_bot, Finset.sum_empty]
    | insert a s ha ih =>
      have hs : (⨆ i ∈ s, E i) ≤ Z := iSup₂_le fun i _ => hZ i
      haveI : FiniteDimensional ℂ ↥(E a) := Submodule.finiteDimensional_of_le (hZ a)
      haveI : FiniteDimensional ℂ ↥(⨆ i ∈ s, E i) := Submodule.finiteDimensional_of_le hs
      have hd : Disjoint (E a) (⨆ i ∈ s, E i) :=
        hE.disjoint_biSup (y := (s : Set J)) fun h => ha (Finset.mem_coe.1 h)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (E a) (⨆ i ∈ s, E i)
      rw [hd.eq_bot, finrank_bot, add_zero, ih] at h
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact h
  have h1 : (⨆ i ∈ (Finset.univ : Finset J), E i) = ⨆ i, E i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← h1]
  exact key Finset.univ

private theorem ze_main (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (Z : Submodule ℂ M) [FiniteDimensional ℂ Z]
    (hZ : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) (P : Module.End ℂ M)
    (hP : ∀ i, ∀ y ∈ Y i, P y ∈ Y i) :
    Module.finrank ℂ ↥(Z ⊓ LinearMap.ker P) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ LinearMap.ker P) := by
  have hE : iSupIndep fun i => Y i ⊓ Z := hY.mono fun _ => inf_le_left
  have h1 := ze_rank (fun i => Y i ⊓ Z) hE Z fun _ => inf_le_right
  have hs : (⨆ i, Y i ⊓ Z) = Z :=
    Submodule.eq_of_le_of_finrank_eq (iSup_le fun _ => inf_le_right) (by rw [h1, hZ])
  have hB : Z ⊓ LinearMap.ker P ≤ ⨆ i, Y i ⊓ (Z ⊓ LinearMap.ker P) := by
    intro F hF
    have hF1 : F ∈ ⨆ i, Y i ⊓ Z := by
      rw [hs]
      exact hF.1
    obtain ⟨x, hx, rfl⟩ := ze_dec (fun i => Y i ⊓ Z) hF1
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨(hx i).1, (hx i).2, ?_⟩
    have h0 : ∑ i, P (x i) = 0 := by
      rw [← map_sum]
      exact hF.2
    exact ze_zero Y hY (fun i => P (x i)) (fun i => hP i _ (hx i).1) h0 i
  have hE' : iSupIndep fun i => Y i ⊓ (Z ⊓ LinearMap.ker P) := hY.mono fun _ => inf_le_left
  haveI : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker P) := Submodule.finiteDimensional_of_le inf_le_left
  have hs' : (⨆ i, Y i ⊓ (Z ⊓ LinearMap.ker P)) = Z ⊓ LinearMap.ker P :=
    le_antisymm (iSup_le fun _ => inf_le_right) hB
  have h := ze_rank (fun i => Y i ⊓ (Z ⊓ LinearMap.ker P)) hE' (Z ⊓ LinearMap.ker P) fun _ => inf_le_right
  rw [hs'] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by rw [inf_assoc]

private theorem ze_opE {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (a : G →₀ ℤ)
    (Y : Submodule ℂ W) (h : ∀ g ∈ a.support, ∀ y ∈ Y, ρ g y ∈ Y) (N : ℕ) :
    ∀ y ∈ Y, (opE ρ a - (N : Module.End ℂ W)) y ∈ Y := by
  intro y hy
  rw [LinearMap.sub_apply]
  refine Y.sub_mem ?_ ?_
  · unfold opE Finsupp.sum
    rw [LinearMap.sum_apply]
    exact Y.sum_mem fun g hg => zsmul_mem (h g hg y hy) _
  · rw [Module.End.natCast_apply]
    exact nsmul_mem hy N

end Abstract

section Gen

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)

private theorem ze_big (g : H.Ga) (hg : Norm H g) : ∀ F ∈ H.Big ι ξ, trF H d g F ∈ H.Big ι ξ := fun F hF => by
  refine ⟨fun i hi γ x => ?_, fun u hu => ?_⟩
  · have := hF.1 i hi γ (x * ((g, 1) : H.Ga × GV n H.Sl))
    rw [← mul_assoc] at this
    exact this
  · obtain ⟨u', hu', e1, e2⟩ := hg.uq u hu
    ext i x k
    have h : ((H.τC ι u' : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec
        fun j => F j (x * ((g, 1) : H.Ga × GV n H.Sl) * ((u' : H.Ga), 1)) k) i =
        F i (x * ((g, 1) : H.Ga × GV n H.Sl)) k :=
      congrFun (congrFun (congrFun (hF.2 u' hu') i) (x * ((g, 1) : H.Ga × GV n H.Sl))) k
    change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec
      fun j => F j (x * ((u : H.Ga), 1) * ((g, 1) : H.Ga × GV n H.Sl)) k) i = F i (x * ((g, 1) : H.Ga × GV n H.Sl)) k
    have e3 : H.τC ι u' = H.τC ι u :=
      congrArg (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))) e2
    have e4 : x * ((u : H.Ga), 1) * ((g, 1) : H.Ga × GV n H.Sl) =
        x * ((g, 1) : H.Ga × GV n H.Sl) * ((u' : H.Ga), 1) := by
      rw [mul_assoc, mul_assoc]
      refine congrArg (x * ·) (Prod.ext ?_ rfl)
      change (u : H.Ga) * g = g * (u' : H.Ga)
      rw [e1, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [e4, ← e3]
    exact h

end Gen

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem ze_infRep (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU L n) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

variable {V : s.Lev} {ι : Qbar l ≃+* ℂ} {lam : Wt L l n} {d : ℕ}
  {e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)}
  {ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ}

private theorem ze_form (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {k : UA L n} (hk : k ∈ finU L n) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    toForm ι e (fun g => F (g * ((away l L n).rangeRestrict k, fun v : V.frame.Vl => cLoc (s.w v.1) k))) ℓ =
      RU L n k (toForm ι e F ℓ) := by
  have h := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.1 F ℓ k
  rw [ze_infRep V ι lam ((finU L n).inv_mem hk)] at h
  exact h.symm

private theorem ze_tr (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (g : Ga l L n) (hg : Norm (hset Q τ₀) g)
    (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (hF : F ∈ YOf Q ι τ₀ e ξ σ) : trF (hset Q τ₀) d g F ∈ YOf Q ι τ₀ e ξ σ := by
  obtain ⟨hb, hw⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  refine (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ _).2 ⟨ze_big (hset Q τ₀) ι ξ g hg F hb, fun i ℓ => ?_⟩
  obtain ⟨k, hk⟩ := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.2.1
    ((g, 1) : Ga l L n × GL' n V)
  have hk' : ((g, 1) : Ga l L n × GL' n V) =
      ((away l L n).rangeRestrict k.1, fun v : V.frame.Vl => cLoc (s.w v.1) k.1) := hk.symm
  change toForm ι e (fun x => F i (x * ((g, 1) : Ga l L n × GL' n V))) ℓ ∈ σ
  rw [hk', ze_form hn Q c τ₀ hξ k.2 (F i) ℓ]
  exact hσ.stable _ _ (hw i ℓ)

end U

section GenE

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {d : ℕ}

private theorem ze_H {J : Type} [Fintype J] (Y : J → Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hY : iSupIndep Y)
    (Z : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hf : FiniteDimensional ℂ Z)
    (hZ : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ)
    (hP : ∀ i, ∀ g ∈ a.support, ∀ y ∈ Y i, trF H d (β g) y ∈ Y i) :
    Module.finrank ℂ ↥(Z ⊓ ePart ((trF H d).comp β) a N) =
      ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ ePart ((trF H d).comp β) a N) :=
  ze_main Y hY Z hZ _ fun i => ze_opE ((trF H d).comp β) a (Y i) (hP i) N

end GenE

theorem UpperTheory.V.Z.Desc.V0.zDecE :
    UpperTheory.V.Z.J.D.ZEq → NormS → ZDecE := by
  intro hE hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hw hs K ev hev J _ σ hσ hind hdec a N ha
  have hZ := UpperTheory.V.Z.J.D.zDec hE l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ A θ x c0 sp hw hs K ev hev J σ hσ hind hdec
  haveI : FiniteDimensional ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) := by
    haveI := hs.fin K c0 le_rfl
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans (iSup_le fun _ => inf_le_left))
  exact ze_H (hset Q τ₀) _ hind _ inferInstance hZ (sec0 n s) a N fun i g hg y hy =>
    ze_tr hn Q c τ₀ hξ (hσ i) _ ((hN l L Ω s n hn V hV Q c m τ₀).norm g (ha g hg)) y hy
