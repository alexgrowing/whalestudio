import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open UpperTheory.V.Z.J.D UpperTheory.V UpperTheory.V.Hi IsLocalRing

private theorem exists_joint_eigenvector_bis {E J : Type} [AddCommGroup E] [Module ℂ E] (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (T : J → Module.End ℂ E) (hst : ∀ i, ∀ w ∈ W, T i w ∈ W) (hc : ∀ i j, ∀ w ∈ W, T i (T j w) = T j (T i w))
    (μ : J → ℂ) (d : ℕ) : ∀ S : Submodule ℂ E, S ≤ W → Module.finrank ℂ S ≤ d → S ≠ ⊥ → (∀ i, ∀ s ∈ S, T i s ∈ S) →
      (∀ i, ∀ s ∈ S, s ∈ (T i).maxGenEigenspace (μ i)) → ∃ G ∈ W, G ≠ 0 ∧ ∀ i, T i G = μ i • G := by
  induction d with
  | zero =>
    intro S hSW hd h0 _ _
    haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSW
    exact absurd (Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)) h0
  | succ d ih =>
    intro S hSW hd h0 hS hG
    haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSW
    by_cases hall : ∀ i, ∀ s ∈ S, (T i - μ i • (1 : Module.End ℂ E)) s = 0
    · obtain ⟨G, hG1, hG2⟩ := (Submodule.ne_bot_iff _).1 h0
      refine ⟨G, hSW hG1, hG2, fun i => ?_⟩
      have := hall i G hG1
      simpa [sub_eq_zero] using this
    · push_neg at hall
      obtain ⟨i, s, hs, hne⟩ := hall
      set D : Module.End ℂ E := T i - μ i • (1 : Module.End ℂ E) with hD
      have hDS : ∀ t ∈ S, D t ∈ S := fun t ht => by
        simp only [hD, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact sub_mem (hS i t ht) (S.smul_mem _ ht)
      have hDp : ∀ (k : ℕ), ∀ t ∈ S, (D ^ k) t ∈ S := by
        intro k
        induction k with
        | zero => intro t ht; simpa using ht
        | succ k ihk => intro t ht; rw [pow_succ', Module.End.mul_apply]; exact hDS _ (ihk t ht)
      let S' : Submodule ℂ E := S ⊓ LinearMap.ker D
      have hlt : S' < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne ?_
        have : s ∈ S' := h ▸ hs
        exact this.2
      have hnz : S' ≠ ⊥ := by
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hG i s hs)
        have hex : ∃ k, (D ^ k) s = 0 := ⟨k, hk⟩
        classical
        have hf := Nat.find_spec hex
        have hf0 : Nat.find hex ≠ 0 := by
          intro h
          rw [h] at hf
          have h1 : s = 0 := by simpa using hf
          exact hne (by rw [h1, map_zero])
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hf0
        have hmin := Nat.find_min hex (m := m) (by omega)
        rw [hm, pow_succ', Module.End.mul_apply] at hf
        exact (Submodule.ne_bot_iff _).2 ⟨_, ⟨hDp m s hs, hf⟩, hmin⟩
      have hcD : ∀ j, ∀ t ∈ S, D (T j t) = T j (D t) := fun j t ht => by
        simp only [hD, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
        rw [hc i j t (hSW ht)]
      refine ih S' (inf_le_left.trans hSW) ?_ hnz (fun j t ht => ⟨hS j t ht.1, ?_⟩) (fun j t ht => hG j t ht.1)
      · have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      · change D (T j t) = 0
        rw [hcD j t ht.1]
        have : D t = 0 := ht.2
        rw [this, map_zero]

private theorem joint_vec {E J : Type} [AddCommGroup E] [Module ℂ E] (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (T : J → Module.End ℂ E) (hst : ∀ i, ∀ w ∈ W, T i w ∈ W) (hc : ∀ i j, ∀ w ∈ W, T i (T j w) = T j (T i w))
    (μ : J → ℂ) (F : E) (hF : F ∈ W) (h0 : F ≠ 0) (hg : ∀ i, F ∈ (T i).maxGenEigenspace (μ i)) :
    ∃ G ∈ W, G ≠ 0 ∧ ∀ i, T i G = μ i • G := by
  have hpw : ∀ i (k : ℕ), ∀ w ∈ W, ((T i - μ i • (1 : Module.End ℂ E)) ^ k) w ∈ W := by
    intro i k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact sub_mem (hst i _ (ih w hw)) (W.smul_mem _ (ih w hw))
  have hcm : ∀ i j (k : ℕ), ∀ w ∈ W, ((T i - μ i • (1 : Module.End ℂ E)) ^ k) (T j w) =
      T j (((T i - μ i • (1 : Module.End ℂ E)) ^ k) w) := by
    intro i j k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih w hw]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
      rw [hc i j _ (hpw i k w hw)]
  refine exists_joint_eigenvector_bis W T hst hc μ _ (W ⊓ ⨅ i, (T i).maxGenEigenspace (μ i)) inf_le_left le_rfl
    ((Submodule.ne_bot_iff _).2 ⟨F, ⟨hF, (Submodule.mem_iInf _).2 hg⟩, h0⟩) (fun j s hs => ?_)
    (fun i s hs => (Submodule.mem_iInf _).1 hs.2 i)
  refine ⟨hst j s hs.1, (Submodule.mem_iInf _).2 fun i => ?_⟩
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hs.2 i)
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  rw [hcm i j k s hs.1, hk, map_zero]

private theorem sp_span {A M E κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup E] [Module ℂ E]
    (P : Submodule A M) (φ : A →+* ℂ) (sp : M → E) (hadd : ∀ f ∈ P, ∀ f' ∈ P, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ P, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A P) :
    Submodule.span ℂ (sp '' P) = Submodule.span ℂ (Set.range fun i => sp (b i)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨f, hf, rfl⟩
    have key : ∀ g : P, sp g ∈ Submodule.span ℂ (Set.range fun i => sp (b i)) := by
      intro g
      have hg : g ∈ Submodule.span A (Set.range b) := by rw [b.span_eq]; trivial
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero =>
        have := hsmul 0 P.zero_mem 0
        simp only [zero_smul, map_zero] at this
        simpa [this] using Submodule.zero_mem _
      | add y y' _ _ h h' =>
        rw [Submodule.coe_add, hadd _ y.2 _ y'.2]
        exact add_mem h h'
      | smul r y _ h =>
        rw [Submodule.coe_smul, hsmul _ y.2]
        exact Submodule.smul_mem _ _ h
    exact key ⟨f, hf⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨b i, (b i).2, rfl⟩

private theorem locPart_sub {A M J : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M] (Z Y : Submodule A M)
    (h : Z ≤ Y) (op : J → Module.End A M) (a : J → A) : locPart Z op a ≤ locPart Y op a := by
  refine inf_le_inf h (iInf_mono fun i => iInf_mono fun k => iSup_mono fun n => ?_)
  exact Submodule.comap_mono (Submodule.smul_mono le_rfl h)

private theorem pow_mem_of {E : Type} [AddCommGroup E] [Module ℂ E] (S : Submodule ℂ E) (T : Module.End ℂ E)
    (c : ℂ) (hS : ∀ s ∈ S, T s ∈ S) (k : ℕ) : ∀ s ∈ S, ((T - c • (1 : Module.End ℂ E)) ^ k) s ∈ S := by
  induction k with
  | zero => intro w hw; simpa using hw
  | succ k ih =>
    intro w hw
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (hS _ (ih w hw)) (S.smul_mem _ (ih w hw))

private theorem abs_main {l : ℕ} [Fact l.Prime] {A M J E : Type} [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module ℂ E] (Y : Submodule A M) [Module.Finite A Y] [Module.Free A Y] (op : J → Module.End A M)
    (hC : CommOn Y op) (e : PadicAlgCl l ≃+* ℂ) (x : A →+* PadicAlgCl l) (hx1 : ∀ b, ‖x b‖ ≤ 1)
    (hx2 : ∀ b ∈ maximalIdeal A, ‖x b‖ < 1) (sp : M → E) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = e (x b) • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent ℂ fun i => sp (b i))
    (opC : J → Module.End ℂ E) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f)) (a : J → A) (μ : J → ℂ)
    (hμ : ∀ i, ‖e.symm (μ i) - x (a i)‖ < 1) :
    (∀ (κ : Type) (b : Module.Basis κ A (locPart Y op a)), LinearIndependent ℂ fun i => sp (b i)) ∧
      Submodule.span ℂ (sp '' Y) ⊓ ⨅ i, (opC i).maxGenEigenspace (μ i) =
        Submodule.span ℂ (sp '' locPart Y op a) ⊓ ⨅ i, (opC i).maxGenEigenspace (μ i) := by
  obtain ⟨hLC, -, hLfin, ⟨Z, hdis, hsup, hZst⟩, hLfree⟩ := AlgebraTools.AnnihilatorQuotientFinite.locFree A M J Y op a hC
  have hLY : locPart Y op a ≤ Y := inf_le_left
  have hZY : Z ≤ Y := hsup ▸ le_sup_right
  haveI : Module.Free A (locPart Y op a) := hLfree inferInstance
  let f : (locPart Y op a × Z) →ₗ[A] Y := (Submodule.inclusion hLY).coprod (Submodule.inclusion hZY)
  have hfb : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨u, v⟩ h
      have h1 : (u : M) + v = 0 := congrArg Subtype.val h
      have h2 : (u : M) ∈ Z := by
        rw [eq_neg_of_add_eq_zero_left h1]
        exact neg_mem v.2
      have h3 : (u : M) = 0 := Submodule.disjoint_def.1 hdis _ u.2 h2
      have h4 : (v : M) = 0 := by simpa [h3] using h1
      exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
    · rintro ⟨y, hy⟩
      rw [← hsup] at hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext rfl⟩
  let g : (locPart Y op a × Z) ≃ₗ[A] Y := LinearEquiv.ofBijective f hfb
  have hgl : ∀ u, ((g (u, 0) : Y) : M) = u := fun u => by
    change ((f (u, 0) : Y) : M) = u
    simp [f]
  have hgr : ∀ v, ((g (0, v) : Y) : M) = v := fun v => by
    change ((f (0, v) : Y) : M) = v
    simp [f]
  let pr : Y →ₗ[A] Z := LinearMap.snd A _ _ ∘ₗ g.symm.toLinearMap
  have hpr : pr ∘ₗ Submodule.inclusion hZY = LinearMap.id := by
    ext v
    have h1 : Submodule.inclusion hZY v = g (0, v) := Subtype.ext (hgr v).symm
    simp [pr, h1]
  haveI hZfin : Module.Finite A Z := Module.Finite.of_surjective pr fun v => ⟨_, LinearMap.congr_fun hpr v⟩
  haveI : Module.Projective A Z := Module.Projective.of_split _ _ hpr
  haveI hZfree : Module.Free A Z := Module.free_of_flat_of_isLocalRing
  have hboth : ∀ (κ κ' : Type) (bL : Module.Basis κ A (locPart Y op a)) (bZ : Module.Basis κ' A Z),
      LinearIndependent ℂ (Sum.elim (fun i => sp (bL i)) (fun j => sp (bZ j))) := by
    intro κ κ' bL bZ
    have := hind _ ((bL.prod bZ).map g)
    convert this using 1
    funext s
    rcases s with i | j
    · simp [Module.Basis.prod_apply, hgl]
    · simp [Module.Basis.prod_apply, hgr]
  let bL0 := Module.Free.chooseBasis A (locPart Y op a)
  let bZ0 := Module.Free.chooseBasis A Z
  have hindL : ∀ (κ : Type) (b : Module.Basis κ A (locPart Y op a)), LinearIndependent ℂ fun i => sp (b i) :=
    fun κ b => (hboth _ _ b bZ0).comp Sum.inl Sum.inl_injective
  have hindZ : ∀ (κ : Type) (b : Module.Basis κ A Z), LinearIndependent ℂ fun i => sp (b i) :=
    fun κ b => (hboth _ _ bL0 b).comp Sum.inr Sum.inr_injective
  refine ⟨hindL, le_antisymm ?_ (inf_le_inf_right _ (Submodule.span_mono (Set.image_mono hLY)))⟩
  have haddL := fun f (hf : f ∈ locPart Y op a) f' (hf' : f' ∈ locPart Y op a) => hadd f (hLY hf) f' (hLY hf')
  have haddZ := fun f (hf : f ∈ Z) f' (hf' : f' ∈ Z) => hadd f (hZY hf) f' (hZY hf')
  have hsmL := fun f (hf : f ∈ locPart Y op a) => hsmul f (hLY hf)
  have hsmZ := fun f (hf : f ∈ Z) => hsmul f (hZY hf)
  set E1 := Submodule.span ℂ (sp '' locPart Y op a) with hE1
  set E2 := Submodule.span ℂ (sp '' Z) with hE2
  have hspanL : E1 = Submodule.span ℂ (Set.range fun i => sp (bL0 i)) :=
    sp_span _ (e.toRingHom.comp x) sp haddL hsmL bL0
  have hspanZ : E2 = Submodule.span ℂ (Set.range fun i => sp (bZ0 i)) :=
    sp_span _ (e.toRingHom.comp x) sp haddZ hsmZ bZ0
  have hdisE : Disjoint E1 E2 := by
    have := (linearIndependent_sum.1 (hboth _ _ bL0 bZ0)).2.2
    rw [hspanL, hspanZ]
    simpa [Function.comp_def] using this
  haveI : FiniteDimensional ℂ E2 := by
    rw [hspanZ]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hst : ∀ (P : Submodule A M), P ≤ Y → (∀ i, ∀ y ∈ P, op i y ∈ P) → ∀ i,
      ∀ w ∈ Submodule.span ℂ (sp '' P), opC i w ∈ Submodule.span ℂ (sp '' P) := by
    intro P hP hPs i w hw
    have : Submodule.span ℂ (sp '' P) ≤ (Submodule.span ℂ (sp '' P)).comap (opC i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      refine Submodule.mem_comap.2 ?_
      rw [← hop i y (hP hy)]
      exact Submodule.subset_span ⟨_, hPs i y hy, rfl⟩
    exact this hw
  have hst1 : ∀ i, ∀ w ∈ E1, opC i w ∈ E1 := hst _ hLY hLC.1
  have hst2 : ∀ i, ∀ w ∈ E2, opC i w ∈ E2 := hst _ hZY hZst
  have hcm : ∀ i j, ∀ w ∈ E2, opC i (opC j w) = opC j (opC i w) := by
    intro i j w hw
    have : E2 ≤ LinearMap.eqLocus (opC i * opC j) (opC j * opC i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      change opC i (opC j (sp y)) = opC j (opC i (sp y))
      rw [← hop j y (hZY hy), ← hop i y (hZY hy), ← hop i _ (hC.1 j y (hZY hy)),
        ← hop j _ (hC.1 i y (hZY hy)), hC.2 i j y (hZY hy)]
    exact this hw
  rintro F ⟨hF1, hF2⟩
  have hle : Submodule.span ℂ (sp '' Y) ≤ E1 ⊔ E2 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ locPart Y op a ⊔ Z := by rw [hsup]; exact hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy'
    rw [hadd u (hLY hu) v (hZY hv)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨v, hv, rfl⟩)
  obtain ⟨F1, h1, F2, h2, rfl⟩ := Submodule.mem_sup.1 (hle hF1)
  have hg2 : ∀ i, F2 ∈ (opC i).maxGenEigenspace (μ i) := by
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hF2 i)
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    rw [map_add] at hk
    have h3 := pow_mem_of E1 (opC i) (μ i) (hst1 i) k F1 h1
    have h4 := pow_mem_of E2 (opC i) (μ i) (hst2 i) k F2 h2
    refine Submodule.disjoint_def.1 hdisE _ ?_ h4
    rw [eq_neg_of_add_eq_zero_right hk]
    exact neg_mem h3
  have hF20 : F2 = 0 := by
    by_contra hne
    obtain ⟨G, hG, hG0, hGe⟩ := joint_vec E2 opC hst2 hcm μ F2 h2 hne hg2
    have hCZ : CommOn Z op := ⟨hZst, fun i j y hy => hC.2 i j y (hZY hy)⟩
    haveI : Fact (CommOn (locPart Z op a) op) := ⟨(AlgebraTools.AnnihilatorQuotientFinite.locFree A M J Z op a hCZ).1⟩
    have h5 := (Up.eigPt Z op hCZ e x hx1 hx2 sp haddZ hsmZ hindZ opC (fun i f hf => hop i f (hZY hf)) G hG hG0 μ hGe a hμ).1
    refine h5 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
    exact Submodule.disjoint_def.1 hdis _ (locPart_sub Z Y hZY op a hy) hy.1
  subst hF20
  rw [add_zero] at hF2 ⊢
  exact ⟨h1, hF2⟩

private theorem sum_lt {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl l) (r : ℝ) (hr : 0 < r)
    (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (h i (Finset.mem_insert_self _ _)) ?_)
    exact ih fun j hj => h j (Finset.mem_insert_of_mem hj)

private theorem root_lt {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] (I : Ideal A) (x : A →+* PadicAlgCl l)
    (hx2 : ∀ b ∈ I, ‖x b‖ < 1) (p : Polynomial A) (hp : p.Monic) (hc : ∀ k, p.coeff k ∈ I ^ (p.natDegree - k))
    (u : PadicAlgCl l) (hu : p.eval₂ x u = 0) : ‖u‖ < 1 := by
  by_contra hge
  have h1 : 1 ≤ ‖u‖ := not_lt.1 hge
  have hpos : 0 < ‖u‖ ^ p.natDegree := pow_pos (lt_of_lt_of_le one_pos h1) _
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hu
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, x (p.coeff i) * u ^ i‖ < ‖u‖ ^ p.natDegree := by
    refine sum_lt _ _ _ hpos fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have h3 : p.coeff i ∈ I := Ideal.pow_le_self (by omega) (hc i)
    rw [norm_mul, norm_pow]
    calc ‖x (p.coeff i)‖ * ‖u‖ ^ i < 1 * ‖u‖ ^ i :=
          mul_lt_mul_of_pos_right (hx2 _ h3) (pow_pos (lt_of_lt_of_le one_pos h1) _)
      _ = ‖u‖ ^ i := one_mul _
      _ ≤ ‖u‖ ^ p.natDegree := pow_le_pow_right₀ h1 hi'.le
  rw [eq_neg_of_add_eq_zero_left hu, norm_neg, norm_pow] at h2
  exact lt_irrefl _ h2

private theorem abs_nil {A P : Type} [CommRing A] [AddCommGroup P] [Module A P] [Module.Finite A P] (I : Ideal A)
    (D : Module.End A P) (h : ∀ y : P, ∃ n : ℕ, (D ^ n) y ∈ I • (⊤ : Submodule A P)) :
    ∃ N : ℕ, LinearMap.range (D ^ N) ≤ I • (⊤ : Submodule A P) := by
  classical
  have hD : ∀ y ∈ I • (⊤ : Submodule A P), D y ∈ I • (⊤ : Submodule A P) := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun y y' h h' => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr trivial
    · rw [map_add]
      exact add_mem h h'
  have hmono : ∀ (n k : ℕ) (y : P), (D ^ n) y ∈ I • (⊤ : Submodule A P) → (D ^ (n + k)) y ∈ I • (⊤ : Submodule A P) := by
    intro n k y hy
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      rw [← add_assoc, pow_succ', Module.End.mul_apply]
      exact hD _ ih
  choose f hf using h
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A P).FG)
  let N := S.sup f
  refine ⟨N, ?_⟩
  have hall : Submodule.span A (S : Set P) ≤ (I • (⊤ : Submodule A P)).comap (D ^ N) := by
    refine Submodule.span_le.2 fun s hs => ?_
    have hle : f s ≤ N := Finset.le_sup hs
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine Submodule.mem_comap.2 ?_
    rw [hk]
    exact hmono _ _ _ (hf s)
  rintro _ ⟨y, rfl⟩
  exact hall (by rw [hS]; trivial)

private theorem abs_cong {l : ℕ} [Fact l.Prime] {A M J : Type} [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M]
    (Y : Submodule A M) [Module.Finite A Y] (op : J → Module.End A M) (hC : CommOn Y op) (a : J → A)
    [hF : Fact (CommOn (locPart Y op a) op)] (x : A →+* PadicAlgCl l) (hx2 : ∀ b ∈ maximalIdeal A, ‖x b‖ < 1)
    (y : heckeAlg (locPart Y op a) op →+* PadicAlgCl l)
    (hy : ∀ b, y (algebraMap A (heckeAlg (locPart Y op a) op) b) = x b) (i : J) :
    ‖y (heckeGen (locPart Y op a) op i) - x (a i)‖ < 1 := by
  obtain ⟨-, hLL, hLfin, -, -⟩ := AlgebraTools.AnnihilatorQuotientFinite.locFree A M J Y op a hC
  let t : heckeAlg (locPart Y op a) op := heckeGen (locPart Y op a) op i - algebraMap A _ (a i)
  let D : Module.End A (locPart Y op a) := t
  have hD : ∀ w : (locPart Y op a), ((D w : (locPart Y op a)) : M) = (op i - algebraMap A (Module.End A M) (a i)) w := by
    intro w
    simp [D, t, heckeGen]
  have hDn : ∀ (n : ℕ) (w : (locPart Y op a)), (((D ^ n) w : (locPart Y op a)) : M) = ((op i - algebraMap A (Module.End A M) (a i)) ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, hD, ih]
  have hnil : ∀ w : (locPart Y op a), ∃ n : ℕ, (D ^ n) w ∈ maximalIdeal A • (⊤ : Submodule A (locPart Y op a)) := by
    intro w
    have hw : (w : M) ∈ locPart (locPart Y op a) op a := by rw [hLL]; exact w.2
    have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw.2 i) 1
    have hmono : Monotone fun n : ℕ =>
        (maximalIdeal A ^ 1 • (locPart Y op a)).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n) := by
      refine monotone_nat_of_le_succ fun n v hv => ?_
      rw [Submodule.mem_comap] at hv ⊢
      rw [pow_succ' (op i - algebraMap A (Module.End A M) (a i)), Module.End.mul_apply]
      refine Submodule.smul_induction_on hv (fun r hr m hm => ?_) (fun u u' h h' => ?_)
      · rw [map_smul]
        refine Submodule.smul_mem_smul hr ?_
        have := hD ⟨m, hm⟩
        rw [← this]
        exact (D ⟨m, hm⟩).2
      · rw [map_add]
        exact add_mem h h'
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 h1
    refine ⟨n, (Submodule.mem_smul_top_iff _ _ _).2 ?_⟩
    rw [hDn]
    simpa using hn
  obtain ⟨N, hN⟩ := abs_nil (maximalIdeal A) D hnil
  obtain ⟨p, hp, -, hc, hz⟩ := LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul A (D ^ N) _ hN
  have hz' : Polynomial.aeval (t ^ N) p = 0 := by
    apply Subtype.ext
    rw [Polynomial.aeval_subalgebra_coe]
    simpa [D] using hz
  have hu : p.eval₂ x (y (t ^ N)) = 0 := by
    have h1 := congrArg y hz'
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h1
    rw [← h1]
    congr 1
    exact RingHom.ext fun b => (hy b).symm
  have h2 := root_lt _ x hx2 p hp hc _ hu
  rw [map_pow, norm_pow] at h2
  have h3 : ‖y t‖ < 1 := by
    by_contra hge
    exact absurd h2 (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))
  have h4 : y t = y (heckeGen (locPart Y op a) op i) - x (a i) := by
    simp only [t, map_sub, hy]
  rwa [h4] at h3

theorem UpperTheory.V.Z.J.D.locSp :
    LocSp := by
  intro L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι x lam d ξ c0 sp hsp K a hF hfree hfin z hz
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfi, hfr, -⟩ := hiComm L Ω l n c H hA A θ hθ K
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI hF' : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hF
  have hcong : ∀ i, ‖ι.symm (ι (z (H.gen θ a K i))) - x.toRingHom (algebraMap c.O A (a i))‖ < 1 := by
    intro i
    rw [RingEquiv.symm_apply_apply]
    exact abs_cong (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC (fun i => algebraMap c.O A (a i)) x.toRingHom hx2
      z.toRingHom (fun b => RingHom.congr_fun hz b) i
  obtain ⟨h1, h2⟩ := abs_main (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) (fun i => algebraMap c.O A (a i)) _ hcong
  refine ⟨h1, ?_⟩
  change H.OrdAt θ ι x.toRingHom lam ξ K c0 ⊓ _ = _
  rw [← hsp.span K c0 le_rfl]
  exact h2
