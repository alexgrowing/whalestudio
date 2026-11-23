import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private def clE {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) (F : M) : Submodule ℂ M where
  carrier := {y | ∀ k ∈ K, ∀ a : ℂ, ρ k F = a • F → ρ k y = a • y}
  add_mem' ha hb k hk a h := by rw [map_add, ha k hk a h, hb k hk a h, smul_add]
  zero_mem' k _ a _ := by simp
  smul_mem' c v hv k hk a h := by rw [map_smul, hv k hk a h, smul_comm]

private theorem clE_stab {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) (F : M) (φ : M →ₗ[ℂ] M)
    (hφ : ∀ k y, ρ k (φ y) = φ (ρ k y)) {y : M} (hy : y ∈ clE ρ K F) : φ y ∈ clE ρ K F := fun k hk a h => by
  rw [hφ, hy k hk a h, map_smul]

private theorem cl_proj {S : Type} [Group S] (ρ : Representation ℂ S M) (U : Subgroup S) [U.FiniteIndex] :
    ∃ P : M →ₗ[ℂ] M, (∀ y ∈ fixd ρ U, ∀ s, ρ s (P y) = P y) ∧ (∀ y, (∀ s, ρ s y = y) → P y = y) ∧
      ∀ Y : Submodule ℂ M, (∀ s, ∀ y ∈ Y, ρ s y ∈ Y) → ∀ y ∈ Y, P y ∈ Y := by
  classical
  haveI : Fintype (S ⧸ U) := Fintype.ofFinite _
  have hc : (Fintype.card (S ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (S ⧸ U) : ℂ)⁻¹ • ∑ q : S ⧸ U, ρ q.out, fun y hy s => ?_, fun y hy => ?_, fun Y hY y hy => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => ?_
    have h1 : (((s • q : S ⧸ U).out : S) : S ⧸ U) = ((s * q.out : S) : S ⧸ U) := by
      rw [QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h2 := hy _ (QuotientGroup.eq.1 h1)
    change ρ s (ρ q.out y) = ρ (s • q : S ⧸ U).out y
    conv_rhs => rw [← h2]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, hy, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    exact Y.smul_mem _ (Y.sum_mem fun q _ => hY _ y hy)

private theorem cl_avg {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) {κ : Type*} (Y : κ → Submodule ℂ M)
    (hst : ∀ i, ∀ k ∈ K, ∀ y ∈ Y i, ρ k y ∈ Y i)
    (hfin : ∀ i, ∀ y ∈ Y i, ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U) {F : M} (hF : F ∈ ⨆ i, Y i) :
    F ∈ ⨆ i, Y i ⊓ clE ρ K F := by
  classical
  by_cases h0 : F = 0
  · rw [h0]; exact zero_mem _
  have hinj : ∀ a b : ℂ, a • F = b • F → a = b := fun a b h => smul_left_injective ℂ h0 h
  have hne : ∀ (g : G) (a : ℂ), ρ g F = a • F → a ≠ 0 := fun g a h ha => h0 (by
    have : ρ g⁻¹ (ρ g F) = F := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [← this, h, ha, zero_smul, map_zero])
  let S : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∃ a : ℂ, ρ k F = a • F}
      one_mem' := ⟨K.one_mem, 1, by simp⟩
      mul_mem' := by
        rintro g h ⟨hg, a, ha⟩ ⟨hh, b, hb⟩
        exact ⟨K.mul_mem hg hh, b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
      inv_mem' := by
        rintro g ⟨hg, a, ha⟩
        refine ⟨K.inv_mem hg, a⁻¹, ?_⟩
        have : ρ g⁻¹ (ρ g F) = F := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha, map_smul] at this
        conv_rhs => rw [← this, smul_smul, inv_mul_cancel₀ (hne g a ha), one_smul] }
  have hS : ∀ s : S, ∃ a : ℂ, ρ s F = a • F := fun s => s.2.2
  choose χ hχ using hS
  let ρ' : Representation ℂ S M :=
    { toFun := fun s => (χ s)⁻¹ • ρ s
      map_one' := by
        have : χ 1 = 1 := hinj _ _ (by rw [← hχ]; simp)
        simp [this]
      map_mul' := fun s t => by
        have : χ (s * t) = χ t * χ s := hinj _ _ (by
          rw [← hχ, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hχ, map_smul, hχ, smul_smul])
        simp [this, smul_smul, mul_comm] }
  have hρ' : ∀ s y, ρ' s y = (χ s)⁻¹ • ρ s y := fun _ _ => rfl
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp Y F).1 hF
  choose U hU hfix using fun i => hfin i (f i) (hf i)
  have hrel : (⨅ i : f.support, U i).relIndex K ≠ 0 := Subgroup.relIndex_iInf_ne_zero fun i => hU i
  have hrel' : (⨅ i : f.support, U i).relIndex S ≠ 0 :=
    fun h => hrel (Subgroup.relIndex_eq_zero_of_le_right (show S ≤ K from fun s hs => hs.1) h)
  haveI : ((⨅ i : f.support, U i).subgroupOf S).FiniteIndex := ⟨hrel'⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := cl_proj ρ' ((⨅ i : f.support, U i).subgroupOf S)
  have hfi : ∀ s ∈ (⨅ i : f.support, U i).subgroupOf S, ∀ i ∈ f.support, ρ s (f i) = f i := fun s hs i hi =>
    hfix i _ (Subgroup.mem_iInf.1 (Subgroup.mem_subgroupOf.1 hs) ⟨i, hi⟩)
  have hχ1 : ∀ s ∈ (⨅ i : f.support, U i).subgroupOf S, χ s = 1 := fun s hs => hinj _ _ (by
    rw [← hχ, one_smul, ← hsum, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl (hfi s hs))
  have hPF : P F = F := hP2 F fun s => by
    rw [hρ', hχ, smul_smul, inv_mul_cancel₀ (hne _ _ (hχ s)), one_smul]
  have : F = ∑ i ∈ f.support, P (f i) := by
    rw [← map_sum, ← hPF, ← hsum]; rfl
  have key : ∀ i ∈ f.support, P (f i) ∈ ⨆ i, Y i ⊓ clE ρ K F := fun i hi => by
    refine Submodule.mem_iSup_of_mem i ⟨hP3 _ (fun s y hy => ?_) _ (hf i), fun k hk a ha => ?_⟩
    · exact (Y i).smul_mem _ (hst i s s.2.1 y hy)
    · have h1 := hP1 (f i) (fun s hs => by rw [hρ', hχ1 s hs, hfi s hs i hi]; simp) ⟨k, hk, a, ha⟩
      have h2 : χ ⟨k, hk, a, ha⟩ = a := hinj _ _ (by rw [← hχ, ← ha])
      rw [hρ', h2] at h1
      conv_rhs => rw [← h1, smul_smul, mul_inv_cancel₀ (hne k a ha), one_smul]
  have h3 := Submodule.sum_mem _ key
  rwa [← this] at h3

private theorem cl_multi {J : Type} [Fintype J] {G : J → Type} [∀ j, Group (G j)] (ρ : ∀ j, Representation ℂ (G j) M)
    (K : ∀ j, Subgroup (G j)) (hc : ∀ j j', j ≠ j' → ∀ g g' y, ρ j g (ρ j' g' y) = ρ j' g' (ρ j g y))
    {κ : Type*} (Y : κ → Submodule ℂ M)
    (hst : ∀ j i, ∀ k ∈ K j, ∀ y ∈ Y i, ρ j k y ∈ Y i)
    (hfin : ∀ j i, ∀ y ∈ Y i, ∃ U : Subgroup (G j), U.relIndex (K j) ≠ 0 ∧ y ∈ fixd (ρ j) U) {F : M} (hF : F ∈ ⨆ i, Y i) :
    F ∈ ⨆ i, Y i ⊓ ⨅ j, clE (ρ j) (K j) F := by
  classical
  have key : ∀ s : Finset J, F ∈ ⨆ i, Y i ⊓ ⨅ j ∈ s, clE (ρ j) (K j) F := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hF
    | insert j s hj ih =>
      have := cl_avg (ρ j) (K j) (fun i => Y i ⊓ ⨅ j ∈ s, clE (ρ j) (K j) F) (fun i k hk y hy => ⟨hst j i k hk y hy.1, ?_⟩)
        (fun i y hy => hfin j i y hy.1) ih
      · refine SetLike.le_def.1 (iSup_mono fun i => le_of_eq ?_) this
        rw [Finset.iInf_insert, inf_assoc, inf_comm (clE (ρ j) (K j) F)]
      · have h2 := hy.2
        simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
        intro j' hj'
        exact clE_stab _ _ _ _ (fun g y => hc j' j (fun h => hj (h ▸ hj')) g k y) (h2 j' hj')
  simpa using key Finset.univ

private theorem cl_iso {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G M}
    {Y : Submodule ℂ M} {σ : SmIrr G} (h : IsoSum ρ Y σ) {y : M} (hy : y ∈ Y) :
    (∀ g, ρ g y ∈ Y) ∧ ∀ K : Subgroup G, IsCompact (K : Set G) → ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U := by
  refine Submodule.iSup_induction _ (motive := fun y => (∀ g, ρ g y ∈ Y) ∧
    ∀ K : Subgroup G, IsCompact (K : Set G) → ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U) (h hy) ?_ ?_ ?_
  · rintro ⟨f, hf, hle⟩ _ ⟨v, rfl⟩
    refine ⟨fun g => hle ⟨_, hf g v⟩, fun K hK => ?_⟩
    let T : Subgroup G :=
      { carrier := {g | σ.ρ g v = v}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : σ.ρ a v = v) (hb : σ.ρ b v = v) => by
          change σ.ρ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} (ha : σ.ρ a v = v) => by
          change σ.ρ a⁻¹ v = v
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have ho : IsOpen (T.subgroupOf K : Set K) := (σ.smooth v).preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    refine ⟨T, Subgroup.index_ne_zero_of_finite, fun u (hu : σ.ρ u v = v) => ?_⟩
    change ρ u (f v) = f v
    rw [← hf, hu]
  · exact ⟨fun g => by simp, fun K _ => ⟨⊤, by simp, zero_mem _⟩⟩
  · intro a b ha hb
    refine ⟨fun g => by rw [map_add]; exact add_mem (ha.1 g) (hb.1 g), fun K hK => ?_⟩
    obtain ⟨U, hU, h1⟩ := ha.2 K hK
    obtain ⟨U', hU', h2⟩ := hb.2 K hK
    exact ⟨U ⊓ U', Subgroup.relIndex_inf_ne_zero hU hU', add_mem (fun u hu => h1 u hu.1) (fun u hu => h2 u hu.2)⟩

private theorem cl_gen {κ : Type*} (Y : κ → Submodule ℂ M) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (T : Module.End ℂ M)
    (hW : ∀ y ∈ W, T y ∈ W) (hY : ∀ i, ∀ y ∈ Y i, T y ∈ Y i) (h : W ≤ ⨆ i, Y i ⊓ W) (μ : ℂ) :
    W ⊓ T.maxGenEigenspace μ ≤ ⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ) := by
  have h1 : ∀ i, Y i ⊓ W ≤ ⨆ ν, (Y i ⊓ W) ⊓ T.maxGenEigenspace ν := fun i => by
    haveI : FiniteDimensional ℂ (Y i ⊓ W : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_right
    have hm : ∀ y ∈ Y i ⊓ W, T y ∈ Y i ⊓ W := fun y hy => ⟨hY i y hy.1, hW y hy.2⟩
    have h0 := congrArg (Submodule.map (Y i ⊓ W).subtype) (Module.End.iSup_maxGenEigenspace_eq_top (T.restrict hm))
    rw [Submodule.map_iSup, Submodule.map_subtype_top] at h0
    refine h0.ge.trans (iSup_mono fun ν => ?_)
    exact (Submodule.inf_genEigenspace T (Y i ⊓ W) hm).ge
  have h2 : W ≤ (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ⊔ ⨆ ν ≠ μ, T.maxGenEigenspace ν := by
    refine h.trans (iSup_le fun i => (h1 i).trans (iSup_le fun ν => ?_))
    by_cases hν : ν = μ
    · subst hν
      rw [inf_assoc]
      exact le_sup_of_le_left (le_iSup (fun i => Y i ⊓ (W ⊓ T.maxGenEigenspace ν)) i)
    · exact le_sup_of_le_right (inf_le_right.trans (le_iSup₂ (f := fun ν (_ : ν ≠ μ) => T.maxGenEigenspace ν) ν hν))
  have h3 : (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ≤ T.maxGenEigenspace μ :=
    iSup_le fun i => inf_le_right.trans inf_le_right
  refine (inf_le_inf_right _ h2).trans ?_
  rw [sup_inf_assoc_of_le _ h3, (T.independent_maxGenEigenspace μ).symm.eq_bot, sup_bot_eq]

private theorem cl_uOp {G : Type} [Group G] (I : Iwa G) (π : Representation ℂ G M) (a : G) (Y : Submodule ℂ M)
    (hY : ∀ g, ∀ y ∈ Y, π g y ∈ Y) : ∀ y ∈ Y, I.uOp π a y ∈ Y := by
  unfold Iwa.uOp
  refine finsum_induction (fun φ : Module.End ℂ M => ∀ y ∈ Y, φ y ∈ Y) (fun y _ => by simp)
    (fun φ ψ h h' y hy => add_mem (h y hy) (h' y hy)) fun q => hY _

end Abstract

private def clSub {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) : Subgroup G where
  carrier := {g | π g y = y}
  one_mem' := by simp
  mul_mem' {a b} (ha : π a y = y) (hb : π b y = y) := by
    change π (a * b) y = y
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} (ha : π a y = y) := by
    change π a⁻¹ y = y
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

private theorem cl_fixd {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) (U : Subgroup G) :
    y ∈ fixd π U ↔ U ≤ clSub π y := Iff.rfl

private theorem cl_pi {J M : Type} [Fintype J] [DecidableEq J] {G : J → Type} [∀ j, Group (G j)] [AddCommGroup M] [Module ℂ M]
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

section Concrete

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ}

private theorem cl_comm (u : H.X.Ub) (b : GV n H.Sl) (F : Fin H.m → H.X.Fn ℂ d) :
    H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m b F) = H.X.rpF ℂ d H.m b (H.X.raF d (H.τC ι) u F) := by
  ext i g k
  change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * ((u : H.Ga), 1) * (1, b)) k) i =
    ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * (1, b) * ((u : H.Ga), 1)) k) i
  simp [mul_assoc]

private theorem cl_fix_rp (U : Subgroup H.X.Ub) (b : GV n H.Sl) :
    ∀ F ∈ fixd (H.X.raF d (H.τC ι)) U, H.X.rpF ℂ d H.m b F ∈ fixd (H.X.raF d (H.τC ι)) U := fun F hF u hu => by
  rw [cl_comm, hF u hu]

private theorem cl_big_rp (ξ : GV n H.Sl →* GL (Fin d) ℂ) (b : GV n H.Sl) :
    ∀ F ∈ H.Big ι ξ, H.X.rpF ℂ d H.m b F ∈ H.Big ι ξ := fun F hF => by
  refine ⟨fun i hi γ g => ?_, cl_fix_rp H ι _ b F hF.2⟩
  have := hF.1 i hi γ (g * (1, b))
  rw [← mul_assoc] at this
  exact this

variable {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l) (lam : Wt L l n)
  (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ)

private theorem cl_mem (F : Fin H.m → H.X.Fn ℂ d) : F ∈ H.ClAt θ ι x lam ξ K e ↔
    F ∈ H.Big ι ξ ∧ F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) ∧ F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N ∧
      F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) ∧ ∀ v i y,
      H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T) F = (ι (H.finPart θ x lam v i y))⁻¹ • F := by
  simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, and_assoc]

private theorem classical_fixed_by_iwahori (c0 : ℕ) (he : c0 ≤ e)
    (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (c0 + 1) →
      H.finPart θ x lam v i y = 1) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x lam ξ K e) :
    F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e) := by
  classical
  obtain ⟨-, -, h1, h2, h3⟩ := (cl_mem H ι θ x lam ξ K e F).1 hF
  rw [cl_fixd] at h1 h2 ⊢
  refine sup_le (sup_le h1 fun t ht => ?_) h2
  refine Subgroup.pi_mem_of_mulSingle_mem t fun v => ?_
  have htv : t v ∈ (glIwa ((H.Sl v).adicCompletion L) n).Tc c0 :=
    (glIwa ((H.Sl v).adicCompletion L) n).Tc_anti he (ht v trivial)
  obtain ⟨y, hy, hy'⟩ := (glBridge ((H.Sl v).adicCompletion L) n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.2.2.2.2
    ⟨t v, (glIwa _ n).Tc_le c0 htv⟩
  have hy1 : t v = _ := hy
  rw [hy1]
  change MonoidHom.mulSingle (fun v : H.V => GLw n (H.Sl v)) v _ ∈ _
  rw [map_list_prod, List.map_ofFn]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
  have := h3 v i (y i)
  rw [triv v i (y i) (hy' c0 htv i), map_one, inv_one, one_smul] at this
  exact this

private theorem cl_stab (c0 : ℕ) (he : c0 ≤ e)
    (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (c0 + 1) →
      H.finPart θ x lam v i y = 1) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x lam ξ K e) :
    H.uzC ι lam d F ∈ H.ClAt θ ι x lam ξ K e := by
  refine Submodule.smul_mem _ _ ?_
  have h0 := (uOpLevel _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) e).1 _ H.X.I.z_mem F (classical_fixed_by_iwahori H ι θ x lam ξ K e c0 he triv F hF)
  obtain ⟨hb, hl, h1, h2, h3⟩ := (cl_mem H ι θ x lam ξ K e F).1 hF
  refine (cl_mem H ι θ x lam ξ K e _).2 ⟨cl_uOp _ _ _ _ (cl_big_rp H ι ξ) F hb, cl_uOp _ _ _ _ (cl_fix_rp H ι _) F hl,
    fun u hu => h0 u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)), fun u hu => h0 u (Subgroup.mem_sup_right hu),
    fun v i y => ?_⟩
  rw [(uOpMul _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) _ _ H.X.I.z_mem H.X.I.z_mem F h1).2.2.2.1 _ (eV n H.Sl v i y).2, h3, map_smul]

private theorem cl_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n e : ℕ) :
    (glIwa k n).N ≤ KO k (Fin n) ∧ (glIwa k n).Nm e ≤ KO k (Fin n) ∧ (glIwa k n).T ≤ KO k (Fin n) := by
  refine ⟨inf_le_right, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h, -, rfl⟩ := hg.2
    exact ⟨h, rfl⟩
  · have h1 : g ∈ (glIwa k n).Iw 0 := Subgroup.mem_sup_left (Subgroup.mem_sup_right hg)
    rw [(glBridge k n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.1] at h1
    exact iwahori_le_KO k _ h1

private theorem cl_back (F y : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x lam ξ K e) (hy : y ∈ H.Big ι ξ)
    (hq : ∀ q, y ∈ clE (H.atW ι d (H.wq q)) (K.1 q) F)
    (hv : ∀ v, y ∈ clE (H.atV d v) (KO ((H.Sl v).adicCompletion L) (Fin n)) F) : y ∈ H.ClAt θ ι x lam ξ K e := by
  classical
  obtain ⟨hb, hl, h1, h2, h3⟩ := (cl_mem H ι θ x lam ξ K e F).1 hF
  have key : ∀ U : ∀ v, Subgroup (GLw n (H.Sl v)), (∀ v, U v ≤ KO ((H.Sl v).adicCompletion L) (Fin n)) →
      F ∈ fixd (H.X.rpF ℂ d H.m) (Subgroup.pi Set.univ U) → y ∈ fixd (H.X.rpF ℂ d H.m) (Subgroup.pi Set.univ U) := by
    intro U hU h
    rw [cl_fixd, Subgroup.pi_le_iff] at h ⊢
    rintro v _ ⟨g, hg, rfl⟩
    have := hv v g (hU v hg) 1 (by rw [one_smul]; exact h v ⟨g, hg, rfl⟩)
    rw [one_smul] at this
    exact this
  refine (cl_mem H ι θ x lam ξ K e _).2 ⟨hy, ?_, key _ (fun v => (cl_KO _ n e).1) h1, key _ (fun v => (cl_KO _ n e).2.1) h2,
    fun v i z => hv v (eT _ n i z : GLw n (H.Sl v)) ((cl_KO _ n e).2.2 (eT _ n i z).2) _ (h3 v i z)⟩
  rw [cl_fixd] at hl ⊢
  refine sup_le hy.2 (iSup_le fun q => ?_)
  rintro _ ⟨g, hg, rfl⟩
  have := hq q g hg 1 (by
    rw [one_smul]
    exact hl (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨g, hg, rfl⟩)))
  rw [one_smul] at this
  exact this

private theorem cl_Yrp (Y : H.Part ι lam ξ) : ∀ g, ∀ y ∈ Y.Y, H.X.rpF ℂ d H.m g y ∈ Y.Y := by
  classical
  exact cl_pi (G := fun v : H.V => GLw n (H.Sl v)) (H.X.rpF ℂ d H.m) Y.Y fun v g z hz => (cl_iso (Y.isoL v) hz).1 g

private theorem cl_Yuz (Y : H.Part ι lam ξ) : ∀ y ∈ Y.Y, H.uzC ι lam d y ∈ Y.Y := fun y hy =>
  Submodule.smul_mem _ _ (cl_uOp H.X.I (H.X.rpF ℂ d H.m) H.X.I.z Y.Y (cl_Yrp H ι lam ξ Y) y hy)

private theorem cl_QQ (hH : H.Ax) (q q' : H.Q) (hq : q ≠ q') (g : GLw n (H.wq q)) (g' : GLw n (H.wq q'))
    (y : Fin H.m → H.X.Fn ℂ d) :
    H.atW ι d (H.wq q) g (H.atW ι d (H.wq q') g' y) = H.atW ι d (H.wq q') g' (H.atW ι d (H.wq q) g y) := by
  change H.X.raF d (H.τC ι) _ (H.X.raF d (H.τC ι) _ y) = H.X.raF d (H.τC ι) _ (H.X.raF d (H.τC ι) _ y)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  exact congrArg (fun z : H.X.Ub => H.X.raF d (H.τC ι) z y) (hH.Q_Q q q' hq g g').eq

private theorem cl_VV (v v' : H.V) (hv : v ≠ v') (g : GLw n (H.Sl v)) (g' : GLw n (H.Sl v'))
    (y : Fin H.m → H.X.Fn ℂ d) : H.atV d v g (H.atV d v' g' y) = H.atV d v' g' (H.atV d v g y) := by
  classical
  change H.X.rpF ℂ d H.m _ (H.X.rpF ℂ d H.m _ y) = H.X.rpF ℂ d H.m _ (H.X.rpF ℂ d H.m _ y)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  exact congrArg (fun z => H.X.rpF ℂ d H.m z y) (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) hv g g').eq

private theorem cl_QV (q : H.Q) (v : H.V) (g : GLw n (H.wq q)) (g' : GLw n (H.Sl v))
    (y : Fin H.m → H.X.Fn ℂ d) : H.atW ι d (H.wq q) g (H.atV d v g' y) = H.atV d v g' (H.atW ι d (H.wq q) g y) :=
  cl_comm H ι (H.sec (H.wq q) g) _ y

private theorem cl_one (hH : H.Ax) {κ : Type 1} (Y : κ → H.Part ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d)
    (hF : F ∈ H.ClAt θ ι x lam ξ K e) (h0 : F ∈ ⨆ i, (Y i).Y) : F ∈ ⨆ i, (Y i).Y ⊓ H.ClAt θ ι x lam ξ K e := by
  have hQ := cl_multi (fun q : H.Q => H.atW ι d (H.wq q)) K.1 (cl_QQ H ι hH)
    (fun i => (Y i).Y) (fun q i k _ y hy => (cl_iso ((Y i).isoQ q) hy).1 k)
    (fun q i y hy => (cl_iso ((Y i).isoQ q) hy).2 _ (K.2 q).2) h0
  have hV := cl_multi (fun v : H.V => H.atV d v) (fun v => KO ((H.Sl v).adicCompletion L) (Fin n)) (cl_VV H)
    (fun i => (Y i).Y ⊓ ⨅ q : H.Q, clE (H.atW ι d (H.wq q)) (K.1 q) F)
    (fun v i k _ y hy => ⟨(cl_iso ((Y i).isoL v) hy.1).1 k, (Submodule.mem_iInf _).2 fun q =>
      clE_stab (H.atW ι d (H.wq q)) (K.1 q) F (H.atV d v k) (fun g z => cl_QV H ι q v g k z)
        ((Submodule.mem_iInf _).1 hy.2 q)⟩)
    (fun v i y hy => (cl_iso ((Y i).isoL v) hy.1).2 _ GlobalTheory.SplitFlip.isCompact_KO) hQ
  refine SetLike.le_def.1 (iSup_mono fun i y hy => ?_) hV
  exact ⟨hy.1.1, cl_back H ι θ x lam ξ K e F y hF ((Y i).le hy.1.1) ((Submodule.mem_iInf _).1 hy.1.2)
    ((Submodule.mem_iInf _).1 hy.2)⟩

end Concrete

theorem UpperTheory.V.Hi.clParts :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    lam ∈ H.admitted → ∀ K e, c0 ≤ e → H.ClAt θ ι x.toRingHom lam ξ K e = ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e ∧ H.OrdAt θ ι x.toRingHom lam ξ K e = ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι P hP x lam d ξ c0 sp hs hlam K e he
  have h1 : H.ClAt θ ι x.toRingHom lam ξ K e ≤
      ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e := by
    intro F hF
    have hF' := (cl_mem H ι θ _ lam ξ K e F).1 hF
    exact cl_one H ι θ _ lam ξ K e hH (fun Y : {Y : H.Part ι lam ξ // P lam Y.r} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨e, classical_fixed_by_iwahori H ι θ _ lam ξ K e c0 he hs.triv F hF⟩)
  refine ⟨le_antisymm h1 (iSup_le fun _ => inf_le_right), le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)⟩
  haveI := hs.fin K e he
  have h2 := cl_gen (fun Y : {Y : H.Part ι lam ξ // P lam Y.r} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K e) (H.uzC ι lam d)
    (cl_stab H ι θ _ lam ξ K e c0 he hs.triv) (fun Y => cl_Yuz H ι lam ξ Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K e ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K e :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K e ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)
