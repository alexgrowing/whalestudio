import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace UpperTheory.GalC.Alg

open Formalism.BasicNotions TensorProduct

variable {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X)

def resA (O : Type) [CommRing O] {X : Type} (S : Set X) : (X → O) →ₐ[O] (S → O) :=
  Pi.algHom O (fun _ : S => O) fun y => Pi.evalAlgHom O (fun _ : X => O) y.1

def cutT : Subalgebra O (S → O) := T.map (resA O S)

def resT : T →ₐ[O] cutT T S := ((resA O S).comp T.val).codRestrict (cutT T S) fun f => ⟨f.1, f.2, rfl⟩

omit [IsDomain O] in
theorem resT_apply (f : T) (y : S) : ((resT T S f : cutT T S) : S → O) y = (f : X → O) y.1 := rfl

omit [IsDomain O] in
theorem resT_surj : Function.Surjective (resT T S) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

def outM : Submodule O M := ⨅ f : {f : T // ∀ y, y ∉ S → (f : X → O) y = 0}, LinearMap.ker (act f.1)

omit [IsDomain O] in
theorem mem_outM {m : M} : m ∈ outM T act S ↔ ∀ f : T, (∀ y, y ∉ S → (f : X → O) y = 0) → act f m = 0 := by
  simp [outM, Submodule.mem_iInf]

abbrev cutM : Type := M ⧸ outM T act S

omit [IsDomain O] in
theorem comm_stable (β : Module.End O M) (h : ∀ f : T, β * act f = act f * β) : outM T act S ≤ (outM T act S).comap β := by
  intro m hm
  rw [Submodule.mem_comap, mem_outM]
  intro f hf
  have := congrArg (fun e : Module.End O M => e m) (h f)
  simp only [Module.End.mul_apply] at this
  rw [← this, (mem_outM T act S).1 hm f hf, map_zero]

def desc (β : Module.End O M) (h : ∀ f : T, β * act f = act f * β) : Module.End O (cutM T act S) :=
  (outM T act S).mapQ (outM T act S) β (comm_stable T act S β h)

omit [IsDomain O] in
theorem desc_mk (β : Module.End O M) (h : ∀ f : T, β * act f = act f * β) (m : M) :
    desc T act S β h ((outM T act S).mkQ m) = (outM T act S).mkQ (β m) := rfl

omit [IsDomain O] in
theorem act_comm (g f : T) : act g * act f = act f * act g := by rw [← map_mul, mul_comm, map_mul]

omit [IsDomain O] in
theorem desc_congr {f g : T} (e : resT T S f = resT T S g) :
    desc T act S (act f) (act_comm T act f) = desc T act S (act g) (act_comm T act g) := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
  rw [desc_mk, desc_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_outM]
  intro k hk
  have z : k * (f - g) = 0 := by
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ S
    · have := congrArg (fun t : cutT T S => (t : S → O) ⟨y, hy⟩) e
      simp only [resT_apply] at this
      simp [this]
    · simp [hk y hy]
  rw [← LinearMap.sub_apply, ← map_sub, ← Module.End.mul_apply, ← map_mul, z, map_zero, LinearMap.zero_apply]

def cutAct : cutT T S →ₐ[O] Module.End O (cutM T act S) :=
  have key : ∀ (b : cutT T S) (f : T), resT T S f = b → ∀ m,
      desc T act S (act (Function.surjInv (resT_surj T S) b)) (act_comm T act _) ((outM T act S).mkQ m) =
        (outM T act S).mkQ (act f m) := fun b f e m => by
    rw [desc_congr T act S ((Function.surjInv_eq (resT_surj T S) b).trans e.symm), desc_mk]
  { toFun := fun b => desc T act S (act (Function.surjInv (resT_surj T S) b)) (act_comm T act _)
    map_one' := LinearMap.ext fun u => by
      obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
      rw [key 1 1 (map_one _), map_one]; rfl
    map_mul' := fun a b => LinearMap.ext fun u => by
      obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
      obtain ⟨f, rfl⟩ := resT_surj T S a
      obtain ⟨g, rfl⟩ := resT_surj T S b
      rw [key _ (f * g) (map_mul _ _ _), Module.End.mul_apply, key _ g rfl, key _ f rfl, map_mul]; rfl
    map_zero' := LinearMap.ext fun u => by
      obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
      rw [key 0 0 (map_zero _), map_zero]; rfl
    map_add' := fun a b => LinearMap.ext fun u => by
      obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
      obtain ⟨f, rfl⟩ := resT_surj T S a
      obtain ⟨g, rfl⟩ := resT_surj T S b
      rw [key _ (f + g) (map_add _ _ _), LinearMap.add_apply, key _ g rfl, key _ f rfl, map_add, LinearMap.add_apply, map_add]
    commutes' := fun c => LinearMap.ext fun u => by
      obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
      rw [key _ (algebraMap O T c) (AlgHom.commutes _ _), AlgHom.commutes, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, map_smul] }

omit [IsDomain O] in
theorem cutAct_mk (f : T) (m : M) : cutAct T act S (resT T S f) ((outM T act S).mkQ m) = (outM T act S).mkQ (act f m) := by
  show desc T act S (act (Function.surjInv (resT_surj T S) _)) (act_comm T act _) _ = _
  rw [desc_congr T act S (Function.surjInv_eq (resT_surj T S) _), desc_mk]

def qK : FractionRing O ⊗[O] M →ₗ[FractionRing O] FractionRing O ⊗[O] cutM T act S :=
  (outM T act S).mkQ.baseChange (FractionRing O)

theorem qK_tmul (a : FractionRing O) (m : M) : qK T act S (a ⊗ₜ m) = a ⊗ₜ (outM T act S).mkQ m := rfl

theorem qK_surj : Function.Surjective (qK T act S) :=
  LinearMap.lTensor_surjective (FractionRing O) (outM T act S).mkQ_surjective

theorem qK_comm {β : Module.End O M} {γ : Module.End O (cutM T act S)}
    (h : ∀ m, γ ((outM T act S).mkQ m) = (outM T act S).mkQ (β m)) (v : FractionRing O ⊗[O] M) :
    γ.baseChange (FractionRing O) (qK T act S v) = qK T act S (β.baseChange (FractionRing O) v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [qK_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, qK_tmul, h]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem qK_act (f : T) (v : FractionRing O ⊗[O] M) :
    (cutAct T act S (resT T S f)).baseChange (FractionRing O) (qK T act S v) =
      qK T act S ((act f).baseChange (FractionRing O) v) := qK_comm T act S (cutAct_mk T act S f) v

theorem qK_desc (β : Module.End O M) (h : ∀ f : T, β * act f = act f * β) (v : FractionRing O ⊗[O] M) :
    (desc T act S β h).baseChange (FractionRing O) (qK T act S v) =
      qK T act S (β.baseChange (FractionRing O) v) := qK_comm T act S (desc_mk T act S β h) v

omit [IsDomain O] in
theorem desc_comm (β : Module.End O M) (h : ∀ f : T, β * act f = act f * β) (b : cutT T S) :
    desc T act S β h * cutAct T act S b = cutAct T act S b * desc T act S β h := by
  obtain ⟨f, rfl⟩ := resT_surj T S b
  refine LinearMap.ext fun u => ?_
  obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
  rw [Module.End.mul_apply, Module.End.mul_apply, cutAct_mk, desc_mk, desc_mk, cutAct_mk, ← Module.End.mul_apply, h f,
    Module.End.mul_apply]

theorem mem_eig {x : X} {v : FractionRing O ⊗[O] M} : v ∈ heckeEig T act x ↔
    ∀ f : T, (act f).baseChange (FractionRing O) v = algebraMap O (FractionRing O) ((f : X → O) x) • v := by
  simp [heckeEig, Submodule.mem_iInf]

theorem exists_sep [Fintype X] (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (x : X) :
    ∃ f : T, (f : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (f : X → O) y = 0 := by
  classical
  have h : ∀ y : X, ∃ g : T, (g : X → O) x ≠ 0 ∧ (y ≠ x → (g : X → O) y = 0) := fun y => by
    by_cases e : y = x
    · exact ⟨1, by simp, fun h => absurd e h⟩
    · obtain ⟨f, hf, hne⟩ := hs x y (Ne.symm e)
      exact ⟨⟨f, hf⟩ - algebraMap O T (f y), by simpa [sub_eq_zero] using hne, fun _ => by simp⟩
  choose g hg using h
  refine ⟨∏ y, g y, ?_, fun y hy => ?_⟩
  · rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => (hg y).1
  · rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) ((hg y).2 hy)

theorem act_mul_K (f g : T) (v : FractionRing O ⊗[O] M) : (act f).baseChange (FractionRing O) ((act g).baseChange (FractionRing O) v) =
    (act (f * g)).baseChange (FractionRing O) v := by
  rw [map_mul, LinearMap.baseChange_mul]; rfl

theorem sep_mem {x : X} {f : T} (hf : ∀ y, y ≠ x → (f : X → O) y = 0) (v : FractionRing O ⊗[O] M) :
    (act f).baseChange (FractionRing O) v ∈ heckeEig T act x := by
  rw [mem_eig]
  intro g
  have e : g * f = (g : X → O) x • f := by
    apply Subtype.ext
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hf y hy]
  rw [act_mul_K, e, map_smul, LinearMap.baseChange_smul, LinearMap.smul_apply, algebraMap_smul]

theorem qK_mem {x : S} {v : FractionRing O ⊗[O] M} (hv : v ∈ heckeEig T act x.1) :
    qK T act S v ∈ heckeEig (cutT T S) (cutAct T act S) x := by
  rw [mem_eig]
  intro b
  obtain ⟨f, rfl⟩ := resT_surj T S b
  rw [qK_act, (mem_eig T act).1 hv f, map_smul, resT_apply]

theorem act_eq_zero_of_qK {v : FractionRing O ⊗[O] M} (hv : qK T act S v = 0) (f : T)
    (hf : ∀ y, y ∉ S → (f : X → O) y = 0) : (act f).baseChange (FractionRing O) v = 0 := by
  let l : cutM T act S →ₗ[O] M := (outM T act S).liftQ (act f) fun m hm => (mem_outM T act S).1 hm f hf
  have : ∀ u, (act f).baseChange (FractionRing O) u = l.baseChange (FractionRing O) (qK T act S u) := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  rw [this, hv, map_zero]

variable [Fintype X] (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y)
include hs

theorem qK_out {x : X} (hx : x ∉ S) {v : FractionRing O ⊗[O] M} (hv : v ∈ heckeEig T act x) : qK T act S v = 0 := by
  obtain ⟨f, h0, h1⟩ := exists_sep T hs x
  have z : resT T S f = 0 := Subtype.ext (funext fun y => h1 y.1 fun e => hx (e ▸ y.2))
  have := qK_act T act S f v
  rw [z, map_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, (mem_eig T act).1 hv f, map_smul] at this
  exact (smul_eq_zero.1 this.symm).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective O _)).2 h0)

theorem qK_inj {x : S} {v : FractionRing O ⊗[O] M} (hv : v ∈ heckeEig T act x.1) (h : qK T act S v = 0) : v = 0 := by
  obtain ⟨f, h0, h1⟩ := exists_sep T hs x.1
  have := act_eq_zero_of_qK T act S h f fun y hy => h1 y fun e => hy (e ▸ x.2)
  rw [(mem_eig T act).1 hv f] at this
  exact (smul_eq_zero.1 this).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective O _)).2 h0)

theorem map_eig (x : S) : (heckeEig T act x.1).map (qK T act S) = heckeEig (cutT T S) (cutAct T act S) x := by
  refine le_antisymm (by rintro _ ⟨v, hv, rfl⟩; exact qK_mem T act S hv) fun u hu => ?_
  obtain ⟨f, h0, h1⟩ := exists_sep T hs x.1
  obtain ⟨v, rfl⟩ := qK_surj T act S u
  have c0 := (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 h0
  refine ⟨(algebraMap O (FractionRing O) ((f : X → O) x.1))⁻¹ • (act f).baseChange (FractionRing O) v,
    Submodule.smul_mem _ _ (sep_mem T act h1 v), ?_⟩
  rw [map_smul, ← qK_act, (mem_eig _ _).1 hu, resT_apply, smul_smul, inv_mul_cancel₀ c0, one_smul]

theorem eig_ne (x : S) (h : heckeEig T act x.1 ≠ ⊥) : heckeEig (cutT T S) (cutAct T act S) x ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨_, qK_mem T act S hv, fun e => h0 (qK_inj T act S hs hv e)⟩

theorem mult_eq (x : S) : heckeMult (cutT T S) (cutAct T act S) x = heckeMult T act x.1 := by
  unfold heckeMult
  rw [← map_eig T act S hs x, ← LinearMap.range_domRestrict]
  refine LinearMap.finrank_range_of_inj ?_
  rw [injective_iff_map_eq_zero]
  exact fun v hv => Subtype.ext (qK_inj T act S hs v.2 hv)

theorem cutAct_inj (hi : Function.Injective act) : Function.Injective (cutAct T act S) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  obtain ⟨g, rfl⟩ := resT_surj T S b
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨f, h0, h1⟩ := exists_sep T hs x.1
  have z : act (f * g) = act 0 := LinearMap.ext fun m => by
    have := cutAct_mk T act S g m
    rw [hb, LinearMap.zero_apply, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_outM] at this
    rw [map_mul, Module.End.mul_apply, this f fun y hy => h1 y fun e => hy (e ▸ x.2), map_zero, LinearMap.zero_apply]
  have := congrArg (fun t : T => (t : X → O) x.1) (hi z)
  simp only [MulMemClass.coe_mul, Pi.mul_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left h0

theorem iSup_eig : ⨆ x, heckeEig T act x = ⊤ := by
  classical
  choose f h0 h1 using exists_sep T hs
  refine top_unique fun v _ => ?_
  let c : X → O := fun x => ∏ y ∈ Finset.univ.erase x, (f y : X → O) y
  have e : (∑ x, c x • f x : T) = algebraMap O T (∏ y, (f y : X → O) y) := by
    apply Subtype.ext
    funext y
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single y]
    · simp [c, Finset.prod_erase_mul]
    · intro x _ hx; simp [h1 x y (Ne.symm hx)]
    · simp
  have d0 : algebraMap O (FractionRing O) (∏ y, (f y : X → O) y) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 (Finset.prod_ne_zero_iff.2 fun y _ => h0 y)
  rw [← Submodule.smul_mem_iff _ d0, algebraMap_smul]
  have : (∏ y, (f y : X → O) y) • v = ∑ x, (act (c x • f x)).baseChange (FractionRing O) v := by
    have a : ∀ s : Finset X, ∑ x ∈ s, (act (c x • f x)).baseChange (FractionRing O) v =
        (act (∑ x ∈ s, c x • f x)).baseChange (FractionRing O) v := fun s => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, map_add, LinearMap.baseChange_add, LinearMap.add_apply]
    rw [a, e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul, LinearMap.baseChange_one]; rfl
  rw [this]
  exact Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (sep_mem T act (fun y hy => by simp [h1 x y hy]) v)

omit hs [Fintype X] in
theorem cutT_local [Nonempty S] [IsLocalRing T] : IsLocalRing (cutT T S) :=
  IsLocalRing.of_surjective' (resT T S).toRingHom (resT_surj T S)

omit hs [Fintype X] in
theorem cutM_tf [Module.IsTorsionFree O M] : Module.IsTorsionFree O (cutM T act S) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c u h => ?_
  obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
  refine or_iff_not_imp_left.2 fun hc => ?_
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_outM] at h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_outM]
  intro f hf
  have := h f hf
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hc

omit hs [Fintype X] in
theorem cutM_free [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M] : Module.Free O (cutM T act S) :=
  haveI := cutM_tf T act S
  inferInstance

end UpperTheory.GalC.Alg
