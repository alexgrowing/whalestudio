import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEigOfInfChar

open Matrix Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.FinalFormK

open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul CompanionTheory.Zuck BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (InLieHpk)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

open Classical in

def ent {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (e : Y.1.ι) (c : X.1.ι) (v : X.2.R.H) : Y.2.R.H :=
  if hv : IsSm (GG k r) X.2.R.σ v then (f (Pi.single c ⟨v, hv⟩) e : Y.2.R.H) else 0

theorem ent_coe {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (e : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    ent f e c v = (f (Pi.single c v) e : Y.2.R.H) := dif_pos v.2

theorem ent_lin {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (e : Y.1.ι) (c : X.1.ι) : Lin (GG k r) X.2.R.σ (ent f e c) :=
  ⟨fun v w hv hw => by
    rw [ent_coe f e c ⟨v, hv⟩, ent_coe f e c ⟨w, hw⟩, ← Submodule.coe_add, ← Pi.add_apply, ← map_add, ← Pi.single_add]
    exact ent_coe f e c (⟨v, hv⟩ + ⟨w, hw⟩), fun a v hv => by
    rw [ent_coe f e c ⟨v, hv⟩, ← Submodule.coe_smul, ← Pi.smul_apply, ← map_smul, ← Pi.single_smul]
    exact ent_coe f e c (a • ⟨v, hv⟩)⟩

theorem nu_zero (U : URep k r) {Ws : List (List (Mx k r))} (hW : ∀ W ∈ Ws, LieWd k r W) : nu U.R.σ Ws 0 = 0 := by
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨W, hW0, rfl⟩ := List.mem_map.1 ha
  have := dsW_smul U.repOn (IsSm.zero (G := GG k r) (σ := U.R.σ)) 0 fun Y hY => hLie Y (hW W hW0 Y hY)
  simpa using this

theorem ent_bdd {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (e : Y.1.ι) (c : X.1.ι) :
    Bdd (GG k r) (InLieHpk k r) X.2.R.σ (ent f e c) := by
  obtain ⟨C, Ws, hW, hb⟩ := hf.cont [] (by simp [LieWd])
  refine ⟨C, Ws, hW, fun v hv => ?_⟩
  rw [ent_coe f e c ⟨v, hv⟩]
  refine le_trans ?_ ((hb (Pi.single c ⟨v, hv⟩)).trans (le_of_eq ?_))
  · rw [sn_eq]
    exact Finset.single_le_sum (f := fun e => ‖dsW Y.2.R.σ [] (f (Pi.single c ⟨v, hv⟩) e : Y.2.R.H)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ e)
  · rw [sum_sn, Finset.sum_eq_single c (fun d _ hd => ?_) (by simp), Pi.single_eq_same]
    rw [Pi.single_eq_of_ne hd]
    exact nu_zero X.2 hW

theorem apply_eq_ent {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (x : M X) (e : Y.1.ι) :
    (f x e : Y.2.R.H) = ∑ c, ent f e c (x c) := by
  conv_lhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun c _ => (ent_coe f e c (x c)).symm

theorem hasDerivAt_rho {F : FRep k r} (hF : F.OK) {Z : Mx k r} (hZ : InLieHpk k r Z) (c d : F.ι) :
    HasDerivAt (fun t => F.ρ (ex Z t) c d) (F.dR Z c d) 0 := by
  obtain ⟨U, Φ, hU, h1U, hΦ, hf⟩ := (show SmOn (GG k r) fun g => F.ρ g c d from hF.smooth c d) 1 (hGG k r).2.1
  exact (hasDerivAt_local (f := fun g => F.ρ g c d) (hLie Z hZ) (ex_zero Z) (hasDerivAt_matrix_exp_zero Z)
    hU h1U hΦ hf).differentiableAt.hasDerivAt

def LR (X : Obj k r) (Z : Mx k r) : Module.End ℂ (M X) := dOp X.1.ι (X.2.dsig Z) + mAct (X.1.dR Z)

theorem LR_coe (X : Obj k r) {Z : Mx k r} (hZ : InLieHpk k r Z) (x : M X) (c : X.1.ι) :
    (LR X Z x c : X.2.R.H) = ds X.2.R.σ Z (x c) + ∑ d, X.1.dR Z c d • (x d : X.2.R.H) := by
  simp only [LR, mAct, dOp, LinearMap.add_apply, Pi.add_apply, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.compLeft_apply, Function.comp_apply, Submodule.coe_add,
    Submodule.coe_sum, Submodule.coe_smul, URep.dsig_coe _ hZ]
  rfl

theorem hasDerivAt_lin {X : Obj k r} (hX : X.1.OK) {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] {T : X.2.R.H → H'} (hl : Lin (GG k r) X.2.R.σ T) (hb : Bdd (GG k r) (InLieHpk k r) X.2.R.σ T)
    {Z : Mx k r} (hZ : InLieHpk k r Z) (x : M X) (c : X.1.ι) :
    HasDerivAt (fun t => T (act X (ex Z t) x c)) (T (LR X Z x c)) 0 := by
  let Tl : X.2.R.smSub →ₗ[ℂ] H' :=
    { toFun := fun v => T v
      map_add' := fun v w => hl.1 _ _ v.2 w.2
      map_smul' := fun a v => hl.2 a _ v.2 }
  have e : (fun t => T (act X (ex Z t) x c)) = fun t => ∑ d, X.1.ρ (ex Z t) c d • T (X.2.R.σ (ex Z t) (x d)) := by
    funext t
    have : act X (ex Z t) x c = ∑ d, X.1.ρ (ex Z t) c d • X.2.sig (ex Z t) (x d) := by
      refine Subtype.ext ?_
      simp only [act_coe X (hLie Z hZ t), Submodule.coe_sum, Submodule.coe_smul, URep.sig_coe _ (hLie Z hZ t)]
    show Tl _ = _
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, ← URep.sig_coe _ (hLie Z hZ t)]
    rfl
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (hasDerivAt_rho hX hZ c d).smul
    (hb.hasDerivAt hl X.2.repOn X.2.rep.2.1 (URep.dense X.2) hLie (x d).2 (hLie Z hZ))
  rw [e]
  refine h1.congr_deriv (Eq.symm ?_)
  have : LR X Z x c = X.2.dsig Z (x c) + ∑ d, X.1.dR Z c d • x d := by
    refine Subtype.ext ?_
    rw [LR_coe X hZ, Submodule.coe_add, URep.dsig_coe _ hZ, Submodule.coe_sum]
    rfl
  show Tl _ = _
  rw [this, map_add, map_sum]
  simp only [ex_zero, hX.one, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, X.2.repOn.map_one, map_smul]
  congr 1
  show T _ = T _
  rw [URep.dsig_coe _ hZ]
  rfl

theorem comm_LR {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) {Z : Mx k r}
    (hZ : InLieHpk k r Z) : f ∘ₗ LR X Z = LR Y Z ∘ₗ f := by
  refine LinearMap.ext fun x => funext fun e => Subtype.ext ?_
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
    hasDerivAt_lin hX (ent_lin f e c) (ent_bdd hf e c) hZ x c
  have h2 := hasDerivAt_lin hY (T := id) ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    ⟨1, [[]], by simp, fun v _ => by simp [nu, dsW]⟩ hZ (f x) e
  simp only [← apply_eq_ent] at h1
  have e1 : (fun t => (f (act X (ex Z t) x) e : Y.2.R.H)) = fun t => id (act Y (ex Z t) (f x) e : Y.2.R.H) :=
    funext fun t => by rw [← LinearMap.comp_apply, hf.equiv _ (hLie Z hZ t)]; rfl
  rw [e1] at h1
  exact h1.unique h2

theorem inLie_reH (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  have h1 : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := PI.HwUniqW.Hpk_mul_self
  have h2 : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := PI.HwUniqW.Hpk_conjTranspose
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  set Hm := Formalism.QuantumDeterminants.Hpk k r
  have e1 : Hm * Y * Hm * Hm = Hm * Y := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : (Hm * Yᴴ * Hm)ᴴ = Hm * Y * Hm := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h2, Matrix.mul_assoc]
  have e4 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold reH
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, e3, e4, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2, ← smul_add]
  simp

theorem inLie_imH (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  have h1 : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := PI.HwUniqW.Hpk_mul_self
  have h2 : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := PI.HwUniqW.Hpk_conjTranspose
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  set Hm := Formalism.QuantumDeterminants.Hpk k r
  have e1 : Hm * Y * Hm * Hm = Hm * Y := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : (Hm * Yᴴ * Hm)ᴴ = Hm * Y * Hm := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h2, Matrix.mul_assoc]
  have e4 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  unfold imH
  rw [sub_neg_eq_add, conjTranspose_smul, conjTranspose_add, e3, e4, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, e1, e2, neg_smul, add_comm (Hm * Y), neg_add_cancel]

theorem L_eq (X : Obj k r) (Z : Mx k r) : L X Z = LR X (reH k r Z) + Complex.I • LR X (imH k r Z) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [L, LR, URep.dC, FRep.dC, mAct, dOp, LinearMap.add_apply, Pi.add_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.compLeft_apply, Function.comp_apply,
    Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, add_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_eq_mul, mul_smul]
  abel

theorem lie_algebra_homomorphism : HomLie := by
  intro k r X Y f hX hY hf Z
  rw [L_eq, L_eq, LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    comm_LR hX hY hf (inLie_reH Z), comm_LR hX hY hf (inLie_imH Z)]

theorem dense_orb {U : URep k r} (hU : U.DS) {w : U.R.H} (hw : w ≠ 0) : Dense (orbSpan (GG k r) U.R.σ w : Set U.R.H) := by
  obtain ⟨ε, μ, h⟩ := hU
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine (CompanionTheory.LimBd.SchurHpk.isIrredOn_of_ds h.2 _ (Submodule.isClosed_topologicalClosure _)
    fun g hg v hv => ?_).resolve_left fun h0 => hw ?_
  · exact map_mem_closure (U.R.σ g).continuous hv fun y hy => apply_mem_orbSpan U.repOn hg hy
  · have hm : w ∈ orbSpan (GG k r) U.R.σ w :=
      Submodule.subset_span ⟨1, U.repOn.one_mem, by simp [U.repOn.map_one]⟩
    have := Submodule.le_topologicalClosure _ hm
    rwa [h0, Submodule.mem_bot] at this

theorem act_one_coe (T : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (y : M (one T)) :
    (act (one T) g y () : T.R.H) = T.R.σ g (y ()) := by
  rw [act_coe (one T) hg]
  show ∑ d : Unit, (1 : Matrix Unit Unit ℂ) () d • T.R.σ g (y d) = _
  simp

theorem ent_one {T : URep k r} {X : Obj k r} (i : M (one T) →ₗ[ℂ] M X) (y : M (one T)) (e : X.1.ι) :
    (i y e : X.2.R.H) = ent i e () (y ()) := by
  rw [apply_eq_ent]
  exact Fintype.sum_unique (M := X.2.R.H) (ι := Unit) fun c => ent i e c (y c)

theorem kerZero' : KerZero := by
  intro k r T X i hT hi y hy hiy
  have hy0 : (y () : T.R.H) ≠ 0 := fun h => hy (funext fun _ => Subtype.ext h)
  refine LinearMap.ext fun x => funext fun e => Subtype.ext ?_
  show (i x e : X.2.R.H) = 0
  rw [ent_one]
  have hl := ent_lin i e ()
  obtain ⟨C, Ws, hW, hb⟩ := ent_bdd hi e ()
  have h0 : ∀ a ∈ orbSpan (GG k r) T.R.σ (y ()), ent i e () a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, hg, rfl⟩ := ha
      show ent i e () (T.R.σ g (y ())) = 0
      rw [← act_one_coe T hg, ← ent_one, ← LinearMap.comp_apply, hi.equiv g hg, LinearMap.comp_apply, hiy, map_zero]
      rfl
    | zero => simpa using hl.2 0 0 IsSm.zero
    | add a b ha hb iha ihb =>
      rw [hl.1 a b (isSm_of_mem_orbSpan T.repOn (y ()).2 ha) (isSm_of_mem_orbSpan T.repOn (y ()).2 hb), iha, ihb,
        add_zero]
    | smul c a ha iha => rw [hl.2 c a (isSm_of_mem_orbSpan T.repOn (y ()).2 ha), iha, smul_zero]
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨a, ha, hxa⟩ := exists_approx (hGG k r) T.repOn T.rep.2.1 (y ()).2 (dense_orb hT hy0) (x ()).2
    (W := Ws.get) (fun j Y hY => hLie Y (hW _ (List.get_mem _ _) Y hY)) (δ := δ / (|C| * Ws.length + 1))
    (by positivity)
  have has := isSm_of_mem_orbSpan T.repOn (y ()).2 ha
  have hd : IsSm (GG k r) T.R.σ ((x () : T.R.H) - a) := IsSm.sub (x ()).2 has
  have e1 : ent i e () (x ()) = ent i e () ((x () : T.R.H) - a) := by
    conv_lhs => rw [← sub_add_cancel (x () : T.R.H) a, hl.1 _ _ hd has, h0 a ha, add_zero]
  rw [e1, zero_add]
  refine (hb _ hd).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (nu_nonneg _ _)).trans ?_)
  have h2 : nu T.R.σ Ws ((x () : T.R.H) - a) ≤ Ws.length * (δ / (|C| * Ws.length + 1)) := by
    rw [nu_eq_sum]
    refine (Finset.sum_le_sum fun j _ => (hxa j).le).trans (le_of_eq ?_)
    simp
  refine (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)).trans ?_
  rw [← mul_assoc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

theorem isInvForm_ent {T T' : URep k r} {f : M (one T) →ₗ[ℂ] M (one T')} (hf : IsHom (one T) (one T') f) :
    IsInvForm T.R T'.R fun x y => ⟪y, ent f () () x⟫_ℂ := by
  have hl := ent_lin f () ()
  obtain ⟨C, Ws, hW, hb⟩ := ent_bdd hf () ()
  refine ⟨fun x hx x' hx' y _ => by beta_reduce; rw [hl.1 x x' hx hx', inner_add_right],
    fun a x hx y _ => by beta_reduce; rw [hl.2 a x hx, inner_smul_right], fun x _ y _ y' _ => inner_add_left _ _ _,
    fun a x _ y _ => inner_smul_left _ _ _, fun g hg x hx y _ => ?_, C, Ws, [[]], fun W hW0 => ?_,
    fun x hx y _ => ?_⟩
  · have : ent f () () (T.R.σ g x) = T'.R.σ g (ent f () () x) := by
      let z : M (one T) := fun _ => ⟨x, hx⟩
      have h1 := ent_one f (act (one T) g z) ()
      rw [act_one_coe T hg, ← LinearMap.comp_apply, hf.equiv g hg, LinearMap.comp_apply, act_one_coe T' hg,
        ent_one] at h1
      exact h1.symm
    beta_reduce
    rw [this]
    exact (⟨(T'.R.σ g : T'.R.H →ₗ[ℂ] T'.R.H), T'.rep.2.1 g hg⟩ : T'.R.H →ₗᵢ[ℂ] T'.R.H).inner_map_map _ _
  · rcases List.mem_append.1 hW0 with h | h
    · exact hW W h
    · rw [List.mem_singleton.1 h]; simp
  · simp only [dsigW_eq', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _)

theorem schur' : Schur := by
  intro hI k r ε S μ T hμ hT
  refine ⟨fun s => ?_, fun s f hf => ?_, fun s t hst f hf => ?_⟩
  · obtain ⟨w, hw0, hw⟩ := exists_kfin (U := T s) ⟨ε, _, hT s⟩
    exact ⟨fun _ => ⟨w, kfin_sm ⟨ε, _, hT s⟩ hw⟩, 0, fun h => hw0 (congrArg Subtype.val (congrFun h ()))⟩
  · obtain ⟨c, hc⟩ := (poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s)).1 _ (isInvForm_ent hf)
    refine ⟨c, LinearMap.ext fun x => funext fun u => Subtype.ext ?_⟩
    show (f x () : (T s).R.H) = c • (x () : (T s).R.H)
    rw [ent_one]
    refine (URep.dense (T s)).eq_of_inner_right (𝕜 := ℂ) fun y hy => ?_
    rw [inner_smul_right]
    exact hc _ (x ()).2 y hy
  · rcases vanish_or_equiv (hT s) (hT t) (isInvForm_ent hf) with h | h
    · refine LinearMap.ext fun x => funext fun u => Subtype.ext ?_
      show (f x () : (T t).R.H) = 0
      rw [ent_one]
      refine (URep.dense (T t)).eq_of_inner_right (𝕜 := ℂ) fun y hy => ?_
      rw [inner_zero_right]
      exact h _ (x ()).2 y hy
    · exact absurd h (CompanionTheory.CapEig.capelli_inequivalence (CompanionTheory.CapEig.coefEig_of_infChar hI) k r ε ε _ _ _ _ _ _
        (hT s).1 (hT t).1 (hT s).2 (hT t).2 fun e => hst (hμ e))

end CompanionTheory.D.gk.FinalFormK
