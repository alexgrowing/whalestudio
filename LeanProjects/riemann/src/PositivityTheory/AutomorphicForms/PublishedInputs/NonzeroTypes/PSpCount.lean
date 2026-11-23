import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spCount

section Abstract

variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]

def eS (H : Subgroup M) (η : M → ℂ) (ρ : Representation ℂ M W) : Submodule ℂ W :=
  ⨅ (m : M) (_ : m ∈ H), LinearMap.ker (ρ m - η m • LinearMap.id)

theorem mem_eS {H : Subgroup M} {η : M → ℂ} {ρ : Representation ℂ M W} {w : W} :
    w ∈ eS H η ρ ↔ ∀ m ∈ H, ρ m w = η m • w := by
  simp only [eS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem rank_eS_le_of_equiv {X : Type} [AddCommGroup X] [Module ℂ X] (H : Subgroup M) (η : M → ℂ)
    {ρ : Representation ℂ M W} {τ : Representation ℂ M X} (φ : ρ.Equiv τ) :
    Module.rank ℂ ↥(eS H η ρ) ≤ Module.rank ℂ ↥(eS H η τ) := by
  have hmem : ∀ w : ↥(eS H η ρ), φ.toLinearEquiv.toLinearMap ((eS H η ρ).subtype w) ∈ eS H η τ := by
    intro w
    rw [mem_eS]
    intro m hm
    have h1 := φ.toIntertwiningMap.isIntertwining _ _ m (w : W)
    have h2 := mem_eS.1 w.2 m hm
    change φ.toLinearEquiv (ρ m w) = τ m (φ.toLinearEquiv w) at h1
    change τ m (φ.toLinearEquiv w) = η m • φ.toLinearEquiv w
    rw [← h1, h2, map_smul]
  let f : ↥(eS H η ρ) →ₗ[ℂ] ↥(eS H η τ) :=
    LinearMap.codRestrict (eS H η τ) (φ.toLinearEquiv.toLinearMap.comp (eS H η ρ).subtype) hmem
  refine LinearMap.rank_le_of_injective f fun x y hxy => ?_
  have : φ.toLinearEquiv (x : W) = φ.toLinearEquiv (y : W) := congrArg Subtype.val hxy
  exact Subtype.ext (φ.toLinearEquiv.injective this)

theorem rank_eS_eq_zero (H : Subgroup M) (η : M → ℂ) (ρ : Representation ℂ M W)
    (hz : ∀ w ∈ eS H η ρ, w = 0) : Module.rank ℂ ↥(eS H η ρ) = 0 := by
  have h : eS H η ρ = ⊥ := eq_bot_iff.2 fun w hw => (Submodule.mem_bot ℂ).2 (hz w hw)
  rw [h, rank_bot]

theorem rank_step {ρ : Representation ℂ M W} (H : Subgroup M) (η : M → ℂ) (S T : Subrepresentation ρ)
    (_hTS : T ≤ S) :
    Module.rank ℂ ↥(eS H η ρ ⊓ S.toSubmodule) ≤
      Module.rank ℂ ↥(eS H η ρ ⊓ T.toSubmodule) + Module.rank ℂ ↥(eS H η (subQuot S T)) := by
  let f : ↥(eS H η ρ ⊓ S.toSubmodule) →ₗ[ℂ]
      (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
    (Submodule.mkQ _).comp (Submodule.inclusion inf_le_right)
  have hrange : LinearMap.range f ≤ eS H η (subQuot S T) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_eS]
    intro m hm
    have hx := mem_eS.1 (Submodule.mem_inf.1 x.2).1 m hm
    change Submodule.Quotient.mk (S.toRepresentation m (Submodule.inclusion inf_le_right x)) =
      η m • Submodule.Quotient.mk (Submodule.inclusion inf_le_right x)
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hx
  have hker : ∀ x : ↥(eS H η ρ ⊓ S.toSubmodule), x ∈ LinearMap.ker f →
      (x : W) ∈ eS H η ρ ⊓ T.toSubmodule := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 x.2).1, ?_⟩
    have h2 : Submodule.inclusion inf_le_right x ∈ T.toSubmodule.comap S.toSubmodule.subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    exact h2
  let g : ↥(LinearMap.ker f) →ₗ[ℂ] ↥(eS H η ρ ⊓ T.toSubmodule) :=
    LinearMap.codRestrict _ (((eS H η ρ ⊓ S.toSubmodule).subtype).comp (LinearMap.ker f).subtype)
      (fun x => hker x.1 x.2)
  have hg : Function.Injective g := by
    intro x y h
    have h' := congrArg (fun z : ↥(eS H η ρ ⊓ T.toSubmodule) => (z : W)) h
    simp only [g] at h'
    exact Subtype.ext (Subtype.ext h')
  calc Module.rank ℂ ↥(eS H η ρ ⊓ S.toSubmodule)
      = Module.rank ℂ ↥(LinearMap.range f) + Module.rank ℂ ↥(LinearMap.ker f) :=
        (LinearMap.rank_range_add_rank_ker f).symm
    _ ≤ Module.rank ℂ ↥(eS H η (subQuot S T)) + Module.rank ℂ ↥(eS H η ρ ⊓ T.toSubmodule) :=
        add_le_add (Submodule.rank_mono hrange) (LinearMap.rank_le_of_injective g hg)
    _ = _ := add_comm _ _

theorem rank_le_of_filtration {ρ : Representation ℂ M W} (H : Subgroup M) (η : M → ℂ) {N : ℕ}
    (S : Fin (N + 1) → Subrepresentation ρ) (hmono : Monotone S) (h0 : S 0 = ⊥)
    (hN : S (Fin.last N) = ⊤) (r : Fin N → Cardinal)
    (hr : ∀ t : Fin N, Module.rank ℂ ↥(eS H η (subQuot (S t.succ) (S t.castSucc))) ≤ r t) :
    Module.rank ℂ ↥(eS H η ρ) ≤ ∑ t, r t := by
  let r' : ℕ → Cardinal := fun u => if h : u < N then r ⟨u, h⟩ else 0
  have key : ∀ j (hj : j < N + 1), Module.rank ℂ ↥(eS H η ρ ⊓ (S ⟨j, hj⟩).toSubmodule) ≤
      ∑ u ∈ Finset.range j, r' u := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h00 : S ⟨0, hj⟩ = ⊥ := h0
      have h' : eS H η ρ ⊓ (S ⟨0, hj⟩).toSubmodule = ⊥ := by
        rw [h00]
        exact inf_bot_eq _
      rw [h', rank_bot]
      exact zero_le
    | succ j ih =>
      intro hj
      have hjN : j < N := by omega
      have hle : S ⟨j, by omega⟩ ≤ S ⟨j + 1, hj⟩ := hmono (Fin.mk_le_mk.2 (Nat.le_succ j))
      have hst := rank_step H η (S ⟨j + 1, hj⟩) (S ⟨j, by omega⟩) hle
      have hq : Module.rank ℂ ↥(eS H η (subQuot (S ⟨j + 1, hj⟩) (S ⟨j, by omega⟩))) ≤ r' j := by
        have := hr ⟨j, hjN⟩
        simp only [r', dif_pos hjN]
        exact this
      rw [Finset.sum_range_succ]
      exact hst.trans (add_le_add (ih (by omega)) hq)
  have hfin := key N (Nat.lt_succ_self N)
  have hNN : S ⟨N, Nat.lt_succ_self N⟩ = ⊤ := hN
  have htop : eS H η ρ ⊓ (S ⟨N, Nat.lt_succ_self N⟩).toSubmodule = eS H η ρ := by
    rw [hNN]
    exact inf_top_eq _
  rw [htop] at hfin
  refine hfin.trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [r', dif_pos t.2]

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eS_jacU_eq {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (η : Levi k m → ℂ) :
    eS (leviK k m) η (jacU e π) = eS (leviK k m) η (jac e π) := by
  ext x
  simp only [mem_eS]
  refine forall₂_congr fun g hg => ?_
  rw [jac, twist_apply, MonoidHom.inv_apply, deltaHalf_of_mem_leviK hg, inv_one, Units.val_one, one_smul]

theorem levi_iwasawa {A B : Type} [Fintype A] [Fintype B] [LinearOrder B] {m : A → Type}
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {c : A → B → Type} [∀ a j, Fintype (c a j)]
    [∀ a j, DecidableEq (c a j)] (g : ∀ a, (Σ j, c a j) ≃ m a) (x : Levi k m) :
    ∃ p ∈ relParab k g, ∃ w ∈ leviK k m, x = p * w := by
  choose p w hw hx using fun a => MultiIrr.exists_parab_mul (g a) (x a)
  refine ⟨fun a => (p a : GL (m a) k), ?_, w, ?_, funext hx⟩
  · exact (Subgroup.mem_pi _).2 fun a _ => (p a).2
  · exact (Subgroup.mem_pi _).2 fun a _ => hw a

theorem eq_zero_of_eval {A B : Type} [Fintype A] [Fintype B] [LinearOrder B] {m : A → Type}
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {c : A → B → Type} [∀ a j, Fintype (c a j)]
    [∀ a j, DecidableEq (c a j)] (g : ∀ a, (Σ j, c a j) ≃ m a) {X : Type} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (relParab k g) X) (η : Levi k m → ℂ)
    (F : smoothPart (ind (relParab k g) τ)) (hF : F ∈ eS (leviK k m) η (smInd (relParab k g) τ))
    (h1 : F.1.1 1 = 0) : F = 0 := by
  have hK : ∀ w ∈ leviK k m, F.1.1 w = 0 := by
    intro w hw
    have h := congrArg (fun F' : smoothPart (ind (relParab k g) τ) => F'.1.1 1) (mem_eS.1 hF w hw)
    change F.1.1 (1 * w) = η w • F.1.1 1 at h
    rw [one_mul, h1, smul_zero] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨p, hp, w, hw, rfl⟩ := levi_iwasawa g x
  have h := F.1.2 ⟨p, hp⟩ w
  change F.1.1 (p * w) = τ ⟨p, hp⟩ (F.1.1 w) at h
  rw [h, hK w hw, map_zero]
  rfl

theorem rank_eS_le {A B : Type} [Fintype A] [Fintype B] [LinearOrder B] {m : A → Type}
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {c : A → B → Type} [∀ a j, Fintype (c a j)]
    [∀ a j, DecidableEq (c a j)] (g : ∀ a, (Σ j, c a j) ≃ m a) {X : Type} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (relParab k g) X) (η : Levi k m → ℂ) :
    Module.rank ℂ ↥(eS (leviK k m) η (smInd (relParab k g) τ)) ≤ Module.rank ℂ X := by
  let ev : ↥(eS (leviK k m) η (smInd (relParab k g) τ)) →ₗ[ℂ] X :=
    { toFun := fun F => (F : smoothPart (ind (relParab k g) τ)).1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearMap.rank_le_of_injective ev fun F F' h => ?_
  have hd : ((F - F' : ↥(eS (leviK k m) η (smInd (relParab k g) τ))) : smoothPart (ind (relParab k g) τ)) = 0 := by
    apply eq_zero_of_eval g τ η _ (F - F').2
    change F.1.1.1 1 - F'.1.1.1 1 = 0
    rw [sub_eq_zero]
    exact h
  exact sub_eq_zero.1 (Subtype.ext hd)

variable {n : ℕ}

abbrev ρc (c : Fin n → kˣ →* ℂˣ) : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
  (ofChar (torusChar c)).comp (leviTorus k (Fin n)).symm.toMonoidHom

theorem isSmooth_ρc (c : Fin n → kˣ →* ℂˣ) (hc : ∀ i, IsSmoothChar (c i)) : IsSmooth (ρc c) := by
  refine isSmooth_comp ((isSmooth_ofChar_iff _).2 ?_) _ ?_
  · unfold torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
      fun i _ => ?_
    exact (hc i).comp _ (continuous_apply i)
  · exact continuous_pi fun i => continuous_glDet.comp (continuous_apply i)

variable (G : Grp k n)

def Good (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a))) : Prop :=
  ∀ i a, bb.1 i a ≠ 0 → a = G.bl i

theorem row_sum (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a))) (i : Fin n) :
    ∑ a, bb.1 i a = 1 := by
  simpa using bb.2.1 i

theorem row_eq (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a))) {i : Fin n}
    {a0 : Fin G.s} (h0 : bb.1 i a0 ≠ 0) (a : Fin G.s) : bb.1 i a = if a = a0 then 1 else 0 := by
  have hs := row_sum G bb i
  have hle : bb.1 i a0 ≤ ∑ a', bb.1 i a' :=
    Finset.single_le_sum (f := fun a' => bb.1 i a') (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0)
  split_ifs with ha
  · subst ha
    omega
  · have h2 : bb.1 i a + bb.1 i a0 ≤ ∑ a', bb.1 i a' := by
      rw [← Finset.sum_pair ha]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

theorem good_unique {bb bb' : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a))}
    (h : Good G bb) (h' : Good G bb') : bb = bb' := by
  have hrow : ∀ x : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a)), Good G x →
      ∀ i a, x.1 i a = if a = G.bl i then 1 else 0 := by
    intro x hx i a
    have hs := row_sum G x i
    have hne : x.1 i (G.bl i) ≠ 0 := by
      intro hz
      have : ∑ a', x.1 i a' = 0 := Finset.sum_eq_zero fun a' _ => by
        by_contra h3
        have := hx i a' h3
        subst this
        exact h3 hz
      omega
    exact row_eq G x hne a
  apply Subtype.ext
  funext i a
  rw [hrow bb h, hrow bb' h']

def cellRep (c : Fin n → kˣ →* ℂˣ)
    (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a)))
    (f : ∀ i, (Σ j, Fin (bb.1 i j)) ≃ (fun _ : Fin n => Unit) i)
    (g : ∀ j, (Σ i, Fin (bb.1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :
    Representation ℂ (relParab k g) (Jacquet (ρc c) (relUnip k f)) :=
  (twist ((relJac f (ρc c)).comp (swapBlocks k (fun i j => Fin (bb.1 i j))))
    (relDeltaHalf k (fun j i => Fin (bb.1 i j)))).comp (relProj k g)

theorem cellRep_apply (c : Fin n → kˣ →* ℂˣ)
    (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a)))
    (f : ∀ i, (Σ j, Fin (bb.1 i j)) ≃ (fun _ : Fin n => Unit) i)
    (g : ∀ j, (Σ i, Fin (bb.1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) (p : relParab k g)
    (v : Jacquet (ρc c) (relUnip k f)) :
    cellRep G c bb f g p v = ((relDeltaHalf k (fun j i => Fin (bb.1 i j)) (relProj k g p) : ℂˣ) : ℂ) •
      relJac f (ρc c) (swapBlocks k (fun i j => Fin (bb.1 i j)) (relProj k g p)) v := rfl

set_option maxHeartbeats 800000 in

theorem cell_char (c : Fin n → kˣ →* ℂˣ)
    (bb : SizeMatrix (fun _ : Fin n => Unit) (fun a : Fin G.s => Fin (G.d a)))
    (f : ∀ i, (Σ j, Fin (bb.1 i j)) ≃ (fun _ : Fin n => Unit) i)
    (g : ∀ j, (Σ i, Fin (bb.1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j)
    (F : smoothPart (ind (relParab k g) (cellRep G c bb f g)))
    (hF : F ∈ eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (smInd (relParab k g) (cellRep G c bb f g)))
    (hne : F ≠ 0) (i0 : Fin n) (a0 : Fin G.s) (h0 : bb.1 i0 a0 ≠ 0) (w : 𝒪[k]ˣ) :
    c i0 (unitIncl k w) = G.μ a0 (unitIncl k w) := by
  classical
  let x : Fin n → 𝒪[k]ˣ := fun i => if i = i0 then w else 1
  let y : ∀ a : Fin G.s, Levi k (fun i : Fin n => Fin (bb.1 i a)) :=
    fun a i => GeneralLinearGroup.scalar (Fin (bb.1 i a)) (unitIncl k (x i))
  have hyK : ∀ a, y a ∈ leviK k (fun i : Fin n => Fin (bb.1 i a)) :=
    fun a => (Subgroup.mem_pi _).2 fun i _ => scalar_mem_KO _
  have hyK' : ∀ i, (fun a => y a i) ∈ leviK k (fun a : Fin G.s => Fin (bb.1 i a)) :=
    fun i => (Subgroup.mem_pi _).2 fun a _ => scalar_mem_KO _
  have hdety : ∀ a i, GeneralLinearGroup.det (y a i) = unitIncl k (x i) ^ bb.1 i a := by
    intro a i
    change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (bb.1 i a)) (unitIncl k (x i))) = _
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  let t : Levi k (fun a : Fin G.s => Fin (G.d a)) := relEmb k g y
  have htP : t ∈ relParab k g := (Subgroup.mem_pi _).2 fun a _ => leviEmb_mem_parab k (g a) (y a)
  have htK : t ∈ leviK k (fun a : Fin G.s => Fin (G.d a)) :=
    (Subgroup.mem_pi _).2 fun a _ => leviEmb_mem_KO (g a) (hyK a)
  have hproj : relProj k g ⟨t, htP⟩ = y := funext fun a => leviProj_leviEmb k (g a) (y a)
  have hF1 : F.1.1 1 ≠ 0 := fun h => hne (eq_zero_of_eval g (cellRep G c bb f g) G.eta F hF h)
  have hE1 : F.1.1 t = G.eta t • F.1.1 1 := by
    have h := congrArg (fun F' : smoothPart (ind (relParab k g) (cellRep G c bb f g)) => F'.1.1 1)
      (mem_eS.1 hF t htK)
    change F.1.1 (1 * t) = G.eta t • F.1.1 1 at h
    rwa [one_mul] at h
  have hd1 : relDeltaHalf k (fun j i => Fin (bb.1 i j)) y = 1 := by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun a _ => deltaHalf_of_mem_leviK (hyK a)
  have hd2 : relDeltaHalf k (fun i j => Fin (bb.1 i j)) (swapBlocks k (fun i j => Fin (bb.1 i j)) y) = 1 := by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ => deltaHalf_of_mem_leviK (hyK' i)
  have hdetz : ∀ i, GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (bb.1 i j)) y) i) =
      unitIncl k (x i) := by
    intro i
    rw [relEmb_apply, det_leviEmb]
    change ∏ a, GeneralLinearGroup.det (y a i) = _
    simp only [hdety]
    rw [Finset.prod_pow_eq_pow_sum, row_sum G bb i, pow_one]
  have hT : torusChar c ((leviTorus k (Fin n)).symm (relEmb k f (swapBlocks k (fun i j => Fin (bb.1 i j)) y))) =
      c i0 (unitIncl k w) := by
    rw [torusChar_apply]
    change ∏ i, c i (GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (bb.1 i j)) y) i)) = _
    simp only [hdetz]
    rw [Finset.prod_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
    simp [x]
  have hdett : ∀ a, GeneralLinearGroup.det (t a) = unitIncl k w ^ bb.1 i0 a := by
    intro a
    change GeneralLinearGroup.det (leviEmb k (g a) (y a)) = _
    rw [det_leviEmb]
    simp only [hdety]
    rw [Finset.prod_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
    simp [x]
  have hEta : G.eta t = ((G.μ a0 (unitIncl k w) : ℂˣ) : ℂ) := by
    unfold Grp.eta
    simp only [hdett, map_pow, Units.val_pow_eq_pow_val]
    rw [Finset.prod_eq_single a0 (fun a _ ha => by rw [row_eq G bb h0 a, if_neg ha, pow_zero]) (by simp),
      row_eq G bb h0 a0, if_pos rfl, pow_one]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (F.1.1 1)
  have key : ((c i0 (unitIncl k w) : ℂˣ) : ℂ) • F.1.1 1 = ((G.μ a0 (unitIncl k w) : ℂˣ) : ℂ) • F.1.1 1 := by
    have h2 : F.1.1 t = cellRep G c bb f g ⟨t, htP⟩ (F.1.1 1) := by
      have h2' := F.1.2 ⟨t, htP⟩ 1
      rw [mul_one] at h2'
      exact h2'
    rw [cellRep_apply, hproj, hd1, Units.val_one, one_smul] at h2
    rw [← hEta, ← hE1, h2, ← hv, relJac_mk, hd2, inv_one, Units.val_one, one_smul]
    change _ = Submodule.Quotient.mk (ofChar (torusChar c)
      ((leviTorus k (Fin n)).symm (relEmb k f (swapBlocks k (fun i j => Fin (bb.1 i j)) y))) v)
    rw [ofChar_apply, hT, ← smul_eq_mul, Submodule.Quotient.mk_smul]
  have h3 := sub_eq_zero.2 key
  rw [← sub_smul, smul_eq_zero] at h3
  rcases h3 with h | h
  · exact Units.ext (sub_eq_zero.1 h)
  · exact absurd h hF1

end Local

end UpperTheory.TNZ.Grp.P_spCount

namespace UpperTheory.TNZ.Grp

open P_spCount

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open scoped Classical in
set_option maxHeartbeats 800000 in

theorem step_spCount {n : ℕ} (G : Grp k n) : G.SpecialCountProp := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩

end UpperTheory.TNZ.Grp
