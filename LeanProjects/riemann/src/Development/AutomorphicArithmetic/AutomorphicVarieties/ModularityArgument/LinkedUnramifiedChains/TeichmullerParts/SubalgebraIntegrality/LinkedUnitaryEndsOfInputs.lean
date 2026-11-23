import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.InfRepFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M] {J : Type} [Fintype J]

private theorem zd_zero (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (x : J → M) (hx : ∀ i, x i ∈ Y i)
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

private theorem zd_dec (D : J → Submodule ℂ M) {F : M} (h : F ∈ ⨆ i, D i) :
    ∃ x : J → M, (∀ i, x i ∈ D i) ∧ ∑ i, x i = F := by
  classical
  induction h using Submodule.iSup_induction' with
  | mem i y hy =>
    refine ⟨Pi.single i y, fun j => ?_, by simp⟩
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simp [Pi.single_eq_of_ne hj]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), by simp [Finset.sum_add_distrib]⟩

private theorem zd_pow (T : Module.End ℂ M) (a : ℂ) (Y : Submodule ℂ M) (h : ∀ y ∈ Y, T y ∈ Y) (k : ℕ) :
    ∀ y ∈ Y, ((T - a • 1) ^ k) y ∈ Y := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    refine ih _ ?_
    have e : (T - a • (1 : Module.End ℂ M)) y = T y - a • y := by simp
    rw [e]
    exact Y.sub_mem (h y hy) (Y.smul_mem a hy)

private theorem zd_gen (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (T : Module.End ℂ M) (a : ℂ)
    (hT : ∀ i, ∀ y ∈ Y i, T y ∈ Y i) (x : J → M) (hx : ∀ i, x i ∈ Y i)
    (h : ∑ i, x i ∈ T.maxGenEigenspace a) (i : J) : x i ∈ T.maxGenEigenspace a := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T a _).1 h
  refine (Module.End.mem_maxGenEigenspace T a _).2 ⟨k, ?_⟩
  exact zd_zero Y hY (fun i => ((T - a • 1) ^ k) (x i)) (fun i => zd_pow T a (Y i) (hT i) k _ (hx i))
    (by rw [← map_sum]; exact hk) i

private theorem zd_rank (E : J → Submodule ℂ M) (hE : iSupIndep E) (Z : Submodule ℂ M) [FiniteDimensional ℂ Z]
    (hZ : ∀ i, E i ≤ Z) : Module.finrank ℂ ↥(⨆ i, E i) = ∑ i, Module.finrank ℂ ↥(E i) := by
  classical
  have key : ∀ s : Finset J, Module.finrank ℂ ↥(⨆ i ∈ s, E i) = ∑ i ∈ s, Module.finrank ℂ ↥(E i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset J), E i) = ⊥ := by simp
      rw [h0]
      simp
    | insert a s ha ih =>
      have hs : (⨆ i ∈ s, E i) ≤ Z := iSup₂_le fun i _ => hZ i
      haveI : FiniteDimensional ℂ ↥(E a) := Submodule.finiteDimensional_of_le (hZ a)
      haveI : FiniteDimensional ℂ ↥(⨆ i ∈ s, E i) := Submodule.finiteDimensional_of_le hs
      have hd : Disjoint (E a) (⨆ i ∈ s, E i) := by
        simpa using hE.disjoint_biSup (y := (s : Set J)) (by simpa using ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (E a) (⨆ i ∈ s, E i)
      rw [hd.eq_bot, finrank_bot, add_zero, ih] at h
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact h
  have h1 : (⨆ i ∈ (Finset.univ : Finset J), E i) = ⨆ i, E i := by simp
  rw [← h1]
  exact key Finset.univ

private theorem zd_main (Y D : J → Submodule ℂ M) (C : Submodule ℂ M) [FiniteDimensional ℂ C] (hY : iSupIndep Y)
    (hDY : ∀ i, D i ≤ Y i) (hDC : ∀ i, D i ≤ C) (hC : C ≤ ⨆ i, D i) (u : Module.End ℂ M)
    (hu : ∀ i, ∀ y ∈ Y i, u y ∈ Y i) (P : ℂ → Prop) {κ : Type} (t : κ → Module.End ℂ M)
    (ht : ∀ i j, ∀ y ∈ D i, t j y ∈ D i) (ev : κ → ℂ) :
    Module.finrank ℂ ↥((⨆ μ : {μ : ℂ // P μ}, C ⊓ u.maxGenEigenspace μ.1) ⊓ ⨅ j, (t j).maxGenEigenspace (ev j)) =
      ∑ i, Module.finrank ℂ ↥(Y i ⊓ ((⨆ μ : {μ : ℂ // P μ}, C ⊓ u.maxGenEigenspace μ.1) ⊓
        ⨅ j, (t j).maxGenEigenspace (ev j))) := by
  set O : Submodule ℂ M := ⨆ μ : {μ : ℂ // P μ}, C ⊓ u.maxGenEigenspace μ.1 with hO
  set Z : Submodule ℂ M := O ⊓ ⨅ j, (t j).maxGenEigenspace (ev j) with hZdef
  have hD : iSupIndep D := hY.mono hDY
  have hOC : O ≤ C := iSup_le fun _ => inf_le_left
  have hA : O ≤ ⨆ i, D i ⊓ O := by
    refine iSup_le fun μ F hF => ?_
    obtain ⟨x, hx, rfl⟩ := zd_dec D (hC hF.1)
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨hx i, ?_⟩
    have h1 := zd_gen Y hY u μ.1 hu x (fun i => hDY i (hx i)) hF.2 i
    exact (le_iSup (fun μ : {μ : ℂ // P μ} => C ⊓ u.maxGenEigenspace μ.1) μ) ⟨hDC i (hx i), h1⟩
  have hB : Z ≤ ⨆ i, Y i ⊓ Z := by
    intro F hF
    obtain ⟨x, hx, rfl⟩ := zd_dec (fun i => D i ⊓ O) (hA hF.1)
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨hDY i (hx i).1, (hx i).2, ?_⟩
    refine (Submodule.mem_iInf _).2 fun j => ?_
    exact zd_gen D hD (t j) (ev j) (fun i => ht i j) x (fun i => (hx i).1) ((Submodule.mem_iInf _).1 hF.2 j) i
  have hE : iSupIndep fun i => Y i ⊓ Z := hY.mono fun _ => inf_le_left
  haveI : FiniteDimensional ℂ ↥Z := Submodule.finiteDimensional_of_le (inf_le_left.trans hOC)
  have hs : (⨆ i, Y i ⊓ Z) = Z := le_antisymm (iSup_le fun _ => inf_le_right) hB
  have h := zd_rank (fun i => Y i ⊓ Z) hE Z fun _ => inf_le_right
  rw [hs] at h
  exact h

private theorem zd_uOp {G : Type} [Group G] (I : Iwa G) (π : Representation ℂ G M) (a : G) (Y : Submodule ℂ M)
    (hY : ∀ g, ∀ y ∈ Y, π g y ∈ Y) : ∀ y ∈ Y, I.uOp π a y ∈ Y := by
  unfold Iwa.uOp
  refine finsum_induction (fun φ : Module.End ℂ M => ∀ y ∈ Y, φ y ∈ Y) (fun y _ => by simp)
    (fun φ ψ h h' y hy => add_mem (h y hy) (h' y hy)) fun q => hY _

private theorem zd_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : Representation ℂ (GL (Fin n) k) M) (j : ℕ) (Y : Submodule ℂ M) (hY : ∀ g, ∀ y ∈ Y, π g y ∈ Y) :
    ∀ y ∈ Y, sphOp π j y ∈ Y := by
  unfold sphOp dc
  refine finsum_induction (fun φ : Module.End ℂ M => ∀ y ∈ Y, φ y ∈ Y) (fun y _ => by simp)
    (fun φ ψ h h' y hy => add_mem (h y hy) (h' y hy)) fun q => hY _

private theorem zd_pi {I : Type} [Fintype I] [DecidableEq I] {G : I → Type} [∀ j, Group (G j)]
    (π : Representation ℂ (∀ j, G j) M) (Y : Submodule ℂ M) (h : ∀ j g, ∀ y ∈ Y, π (Pi.mulSingle j g) y ∈ Y) :
    ∀ g, ∀ y ∈ Y, π g y ∈ Y := by
  let S : Subgroup (∀ j, G j) :=
    { carrier := {g | (∀ y ∈ Y, π g y ∈ Y) ∧ ∀ y ∈ Y, π g⁻¹ y ∈ Y}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => ⟨fun y hy => by rw [map_mul]; exact ha.1 _ (hb.1 y hy),
        fun y hy => by rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 y hy)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩ }
  intro g
  have : g ∈ S := Subgroup.pi_mem_of_mulSingle_mem g fun j => ⟨h j _, by rw [← Pi.mulSingle_inv]; exact h j _⟩
  exact this.1

private def zdSt {G : Type} [Group G] (π : Representation ℂ G M) (y : M) : Subgroup G where
  carrier := {g | π g y = y}
  one_mem' := by simp
  mul_mem' {a b} (ha : π a y = y) (hb : π b y = y) := by
    change π (a * b) y = y
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} (ha : π a y = y) := by
    change π a⁻¹ y = y
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

private theorem zd_fix {G : Type} [Group G] (π : Representation ℂ G M) (y : M) (U : Subgroup G) :
    y ∈ fixd π U ↔ U ≤ zdSt π y := Iff.rfl

end Abstract

section Gen

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ}
  {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l) (lam : Wt L l n)
  (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ)

private theorem zd_cl (F : Fin H.m → H.X.Fn ℂ d) : F ∈ H.ClAt θ ι x lam ξ K e ↔
    F ∈ H.Big ι ξ ∧ F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) ∧ F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N ∧
      F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) ∧ ∀ v i y,
      H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T) F = (ι (H.finPart θ x lam v i y))⁻¹ • F := by
  simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, and_assoc]

private theorem zero_dim_mem_iwahori_fixed
    (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (e + 1) →
      H.finPart θ x lam v i y = 1) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x lam ξ K e) :
    F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e) := by
  classical
  obtain ⟨-, -, h1, h2, h3⟩ := (zd_cl H ι θ x lam ξ K e F).1 hF
  rw [zd_fix] at h1 h2 ⊢
  refine sup_le (sup_le h1 fun t ht => ?_) h2
  refine Subgroup.pi_mem_of_mulSingle_mem t fun v => ?_
  have htv : t v ∈ (glIwa ((H.Sl v).adicCompletion L) n).Tc e := ht v trivial
  obtain ⟨y, hy, hy'⟩ := (glBridge ((H.Sl v).adicCompletion L) n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.2.2.2.2
    ⟨t v, (glIwa _ n).Tc_le e htv⟩
  have hy1 : t v = _ := hy
  rw [hy1]
  change MonoidHom.mulSingle (fun v : H.V => GLw n (H.Sl v)) v _ ∈ _
  rw [map_list_prod, List.map_ofFn]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
  have := h3 v i (y i)
  rw [triv v i (y i) (hy' e htv i), map_one, inv_one, one_smul] at this
  exact this

private theorem zd_comm (u : H.X.Ub) (b : GV n H.Sl) (F : Fin H.m → H.X.Fn ℂ d) :
    H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m b F) = H.X.rpF ℂ d H.m b (H.X.raF d (H.τC ι) u F) := by
  ext i g k
  change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * ((u : H.Ga), 1) * (1, b)) k) i =
    ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * (1, b) * ((u : H.Ga), 1)) k) i
  simp [mul_assoc]

private theorem zd_big (b : GV n H.Sl) :
    ∀ F ∈ H.Big ι ξ, H.X.rpF ℂ d H.m b F ∈ H.Big ι ξ := fun F hF => by
  refine ⟨fun i hi γ g => ?_, fun u hu => ?_⟩
  · have := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at this
    exact this
  · rw [zd_comm, hF.2 u hu]

private theorem zd_C {J : Type} [Fintype J] (Y : J → Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hY : iSupIndep Y)
    (hB : ∀ i, Y i ≤ H.Big ι ξ) (hrp : ∀ i g, ∀ y ∈ Y i, H.X.rpF ℂ d H.m g y ∈ Y i) (hq : IsEmpty H.Q)
    (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (e + 1) →
      H.finPart θ x lam v i y = 1)
    (hdec : H.Big ι ξ ⊓ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e) ≤ ⨆ i, Y i ⊓ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) :
    H.ClAt θ ι x lam ξ K e ≤ ⨆ i, Y i ⊓ H.ClAt θ ι x lam ξ K e := by
  intro F hF
  have hI := zero_dim_mem_iwahori_fixed H ι θ x lam ξ K e triv F hF
  obtain ⟨hb, -, -, -, h3⟩ := (zd_cl H ι θ x lam ξ K e F).1 hF
  obtain ⟨y, hy, rfl⟩ := zd_dec _ (hdec ⟨hb, hI⟩)
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨(hy i).1, ?_⟩
  have hlev : H.lev K = H.UQ := by
    unfold HSet.lev
    rw [iSup_of_empty]
    exact sup_bot_eq _
  refine (zd_cl H ι θ x lam ξ K e _).2 ⟨hB i (hy i).1, ?_, fun u hu => (hy i).2 u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)),
    fun u hu => (hy i).2 u (Subgroup.mem_sup_right hu), fun v a z => ?_⟩
  · rw [hlev]
    exact (hB i (hy i).1).2
  · have h := h3 v a z
    rw [map_sum, Finset.smul_sum] at h
    refine sub_eq_zero.1 (zd_zero Y hY (fun i => H.X.rpF ℂ d H.m (eV n H.Sl v a z : H.X.I.T) (y i) -
      (ι (H.finPart θ x lam v a z))⁻¹ • y i) (fun i => (Y i).sub_mem (hrp i _ _ (hy i).1) ((Y i).smul_mem _ (hy i).1)) ?_ i)
    rw [Finset.sum_sub_distrib, h, sub_self]

private theorem zd_H {J : Type} [Fintype J] (Y : J → Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hY : iSupIndep Y)
    (hB : ∀ i, Y i ≤ H.Big ι ξ) (hrp : ∀ i g, ∀ y ∈ Y i, H.X.rpF ℂ d H.m g y ∈ Y i) (hq : IsEmpty H.Q)
    (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (e + 1) →
      H.finPart θ x lam v i y = 1)
    (hdec : H.Big ι ξ ⊓ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e) ≤ ⨆ i, Y i ⊓ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e))
    (hfin : FiniteDimensional ℂ (H.ClAt θ ι x lam ξ K e)) (ev : H.Op → ℂ)
    (hop : ∀ i j, ∀ y ∈ Y i ⊓ H.ClAt θ ι x lam ξ K e, H.opC ι lam d j y ∈ Y i ⊓ H.ClAt θ ι x lam ξ K e) :
    Module.finrank ℂ (zPart H θ ι x lam ξ K e ev) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ zPart H θ ι x lam ξ K e ev) :=
  zd_main Y (fun i => Y i ⊓ H.ClAt θ ι x lam ξ K e) (H.ClAt θ ι x lam ξ K e) hY (fun _ => inf_le_left)
    (fun _ => inf_le_right) (zd_C H ι θ x lam ξ K e Y hY hB hrp hq triv hdec) (H.uzC ι lam d)
    (fun i y hy => Submodule.smul_mem _ _ (zd_uOp H.X.I (H.X.rpF ℂ d H.m) H.X.I.z (Y i) (hrp i) y hy))
    (fun μ => ‖ι.symm μ‖ = 1) (H.opC ι lam d) hop ev

end Gen

section Conc

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) (m : ℕ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

private def wS (σ : Submodule ℂ (UA L n → ℂ)) :
    Submodule ℂ (Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) where
  carrier := {F | ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ}
  add_mem' {x y} hx hy i ℓ := by
    have : toForm ι e ((x + y) i) ℓ = toForm ι e (x i) ℓ + toForm ι e (y i) ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add]
    rw [this]
    exact σ.add_mem (hx i ℓ) (hy i ℓ)
  zero_mem' i ℓ := by
    have : toForm ι e ((0 : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) i) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]
    exact σ.zero_mem
  smul_mem' a x hx i ℓ := by
    have : toForm ι e ((a • x) i) ℓ = a • toForm ι e (x i) ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]
    exact σ.smul_mem a (hx i ℓ)

private theorem zd_under (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

variable {m} {c : Coef l} (hn : 1 ≤ n) (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
  {ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ} (hξ : IsBasis ι e ξ)
  {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)

include hn hξ hσ

private theorem zd_atV (v : V.frame.Vl) (g : GLw n (s.w v.1)) :
    ∀ F ∈ wS ι m e σ, (hset Q τ₀).atV d v g F ∈ wS ι m e σ := by
  intro F hF i ℓ
  have hsp : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA v.1) (s.split v.1 (Or.inl v.2)) _ (zd_under s v.1)
  obtain ⟨j, hj1, hj2, -⟩ := (secU l L Ω s n hn (s.w v.1) hsp).1
  have h := UpperTheory.V.Hi.partUR2AtV l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ v j hj1 hj2 F g i ℓ
  rw [h]
  exact hσ.stable (j g) _ (hF i ℓ)

private theorem zd_atW (w : Plc L) (hsp : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) :
    ∀ F ∈ wS ι m e σ, (hset Q τ₀).atW ι d w g F ∈ wS ι m e σ := by
  intro F hF i ℓ
  obtain ⟨j, hj1, hj2, -⟩ := (secU l L Ω s n hn w hsp).1
  have h := UpperTheory.V.Hi.partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ w hsp hS j hj1 hj2 F g i ℓ
  rw [h]
  exact hσ.stable (j g) _ (hF i ℓ)

private theorem zd_rp (g : GV n (fun v : V.frame.Vl => s.w v.1)) :
    ∀ F ∈ wS ι m e σ, (hset Q τ₀).X.rpF ℂ d m g F ∈ wS ι m e σ := by
  classical
  exact zd_pi (G := fun v : V.frame.Vl => GLw n (s.w v.1)) ((hset Q τ₀).X.rpF ℂ d m) (wS ι m e σ)
    (fun v g y hy => zd_atV ι e hn Q τ₀ hξ hσ v g y hy) g

end Conc

theorem UpperTheory.V.Z.J.D.zDec :
    ZEq → ZDec := by
  intro _ l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp _ hs K ev _ J _ σ hσ hind hdec
  have hq : IsEmpty (hset Q τ₀).Q := ⟨fun q => by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rw [hV] at h
    exact Q.notS q h⟩
  have hM := fun σ' => UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ'
  have hrp : ∀ i g, ∀ y ∈ YOf Q ι τ₀ e ξ (σ i), (hset Q τ₀).X.rpF ℂ d m g y ∈ YOf Q ι τ₀ e ξ (σ i) := fun i g y hy =>
    (hM _ _).2 ⟨zd_big (hset Q τ₀) ι ξ g y ((hM _ y).1 hy).1, zd_rp ι e hn Q τ₀ hξ (hσ i) g y ((hM _ y).1 hy).2⟩
  refine zd_H (hset Q τ₀) ι θ x.toRingHom lam ξ K c0 _ hind (fun i y hy => hy.1) hrp hq hs.triv hdec
    (hs.fin K c0 le_rfl) ev ?_
  intro i j y hy
  have hc := hs.stab K c0 le_rfl j y hy.2
  refine ⟨(hM _ _).2 ⟨((zd_cl (hset Q τ₀) ι θ x.toRingHom lam ξ K c0 _).1 hc).1, ?_⟩, hc⟩
  have hw := ((hM _ y).1 hy.1).2
  rcases j with p | p
  · exact zd_sph ((hset Q τ₀).atW ι d p.1.1) (p.2 + 1) (wS ι m e (σ i))
      (zd_atW ι e hn Q τ₀ hξ (hσ i) p.1.1 p.1.2.2 fun h => p.1.2.1 (hV.symm ▸ h)) y hw
  · exact (wS ι m e (σ i)).smul_mem _
      (zd_uOp (hset Q τ₀).X.I ((hset Q τ₀).X.rpF ℂ d m) _ (wS ι m e (σ i)) (fun g => zd_rp ι e hn Q τ₀ hξ (hσ i) g) y hw)
