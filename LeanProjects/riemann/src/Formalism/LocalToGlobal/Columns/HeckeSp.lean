import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.DecoFin

noncomputable section

namespace Formalism.L2.Col

open Module Module.End Formalism.L2.NCov

section Eig

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]

def eigAt (op : I → End K V) (x : I → K) : Submodule K V :=
  ⨅ i, (op i).maxGenEigenspace (x i)

def Occurs (op : I → End K V) (x : I → K) : Prop := eigAt op x ≠ ⊥

def eigSum (op : I → End K V) (C : (I → K) → Prop) : Submodule K V :=
  ⨆ (x : I → K) (_ : C x), eigAt op x

def PairComm (op : I → End K V) : Prop := ∀ i j, Commute (op i) (op j)

def SplitOver (op : I → End K V) : Prop := ∀ i, ⨆ μ, (op i).maxGenEigenspace μ = ⊤

variable {op : I → End K V}

theorem eigAt_le (op : I → End K V) (x : I → K) (i : I) : eigAt op x ≤ (op i).maxGenEigenspace (x i) :=
  iInf_le (fun i => (op i).maxGenEigenspace (x i)) i

theorem eigAt_le_eigSum {C : (I → K) → Prop} {x : I → K} (h : C x) : eigAt op x ≤ eigSum op C :=
  le_iSup₂_of_le (f := fun x (_ : C x) => eigAt op x) x h le_rfl

theorem mem_eigAt_of_forall_apply {x : I → K} {v : V} (h : ∀ i, op i v = x i • v) : v ∈ eigAt op x := by
  rw [eigAt, Submodule.mem_iInf]
  intro i
  rw [mem_maxGenEigenspace]
  exact ⟨1, by simp [h i]⟩

theorem eigAt_eq_iInf_eigenspace (hss : ∀ i, (op i).IsFinitelySemisimple) (x : I → K) :
    eigAt op x = ⨅ i, (op i).eigenspace (x i) :=
  iInf_congr fun i => (hss i).maxGenEigenspace_eq_eigenspace (x i)

theorem eq_of_occurs_of_le {x : I → K} (hx : Occurs op x) {i : I} {a : K}
    (h : eigAt op x ≤ (op i).maxGenEigenspace a) : x i = a :=
  eq_of_le_maxGen hx (eigAt_le op x i) h

theorem Occurs.eq_one {x : I → K} (hx : Occurs op x) {i : I} (hi : op i = 1) : x i = 1 := by
  refine eq_of_occurs_of_le hx ?_
  have := maxGen_smul_one (K := K) (V := V) 1
  rw [one_smul] at this
  rw [hi, this]
  exact le_top

theorem iSupIndep_eigAt (hc : PairComm op) : iSupIndep (eigAt op) :=
  independent_iInf_maxGenEigenspace_of_forall_mapsTo op
    fun i j φ => mapsTo_maxGenEigenspace_of_comm (hc j i) φ

theorem iSup_eigAt_eq_top [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op) :
    ⨆ x, eigAt op x = ⊤ :=
  iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute op
    (fun i j _ => hc i j) hs

theorem exists_finset_occurs [FiniteDimensional K V] (hc : PairComm op) :
    ∃ F : Finset (I → K), ∀ x, Occurs op x ↔ x ∈ F := by
  have hfin := Submodule.finite_ne_bot_of_iSupIndep (iSupIndep_eigAt hc)
  exact ⟨hfin.toFinset, fun x => (hfin.mem_toFinset).symm⟩

theorem eigSum_eq_sup {F : Finset (I → K)} (hF : ∀ x, Occurs op x ↔ x ∈ F) (C : (I → K) → Prop)
    [DecidablePred C] : eigSum op C = (F.filter C).sup (eigAt op) :=
  iSup_eq_sup_filter (eigAt op) F (fun x h => (hF x).1 h) C

theorem eigSum_mono {C C' : (I → K) → Prop} (h : ∀ x, C x → C' x) : eigSum op C ≤ eigSum op C' :=
  iSup₂_le fun _ hx => eigAt_le_eigSum (h _ hx)

theorem eigSum_congr {C C' : (I → K) → Prop} (h : ∀ x, Occurs op x → (C x ↔ C' x)) :
    eigSum op C = eigSum op C' := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    by_cases h0 : eigAt op x = ⊥
    · rw [h0]; exact bot_le
    · exact eigAt_le_eigSum ((h x h0).1 hx)
  · refine iSup₂_le fun x hx => ?_
    by_cases h0 : eigAt op x = ⊥
    · rw [h0]; exact bot_le
    · exact eigAt_le_eigSum ((h x h0).2 hx)

theorem eigSum_or (C C' : (I → K) → Prop) :
    eigSum op (fun x => C x ∨ C' x) = eigSum op C ⊔ eigSum op C' := by
  simp only [eigSum, iSup_or, iSup_sup_eq]

theorem eigSum_false : eigSum op (fun _ => False) = ⊥ := by simp [eigSum]

theorem eigSum_true [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op) :
    eigSum op (fun _ => True) = ⊤ := by
  simpa [eigSum] using iSup_eigAt_eq_top hc hs

theorem disjoint_eigSum [FiniteDimensional K V] (hc : PairComm op) {C C' : (I → K) → Prop}
    (h : ∀ x, C x → ¬ C' x) : Disjoint (eigSum op C) (eigSum op C') := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_occurs hc
  rw [eigSum_eq_sup hF, eigSum_eq_sup hF]
  exact ((iSupIndep_eigAt hc).supIndep' F).disjoint_sup_sup (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) (Finset.disjoint_filter.2 fun x _ h1 h2 => h x h1 h2)

theorem isCompl_eigSum [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) : IsCompl (eigSum op C) (eigSum op fun x => ¬ C x) := by
  refine ⟨disjoint_eigSum hc fun x h h' => h' h, ?_⟩
  rw [codisjoint_iff, ← eigSum_or, ← eigSum_true hc hs]
  exact eigSum_congr fun x _ => ⟨fun _ => trivial, fun _ => em _⟩

theorem eigSum_and [FiniteDimensional K V] (hc : PairComm op) (C C' : (I → K) → Prop) :
    eigSum op (fun x => C x ∧ C' x) = eigSum op C ⊓ eigSum op C' := by
  have e : eigSum op C = eigSum op (fun x => C x ∧ C' x) ⊔ eigSum op (fun x => C x ∧ ¬ C' x) := by
    rw [← eigSum_or]
    exact eigSum_congr fun x _ => by tauto
  have hd : Disjoint (eigSum op fun x => C x ∧ ¬ C' x) (eigSum op C') :=
    disjoint_eigSum hc fun x h h' => h.2 h'
  rw [e, sup_inf_assoc_of_le _ (eigSum_mono fun x h => h.2), hd.eq_bot, sup_bot_eq]

theorem finrank_eigSum [FiniteDimensional K V] (hc : PairComm op) {F : Finset (I → K)}
    (hF : ∀ x, Occurs op x ↔ x ∈ F) (C : (I → K) → Prop) [DecidablePred C] :
    finrank K (eigSum op C) = ∑ x ∈ F.filter C, finrank K (eigAt op x) := by
  rw [eigSum_eq_sup hF, finrank_finset_sup (iSupIndep_eigAt hc)]

theorem eigSum_ne_bot {C : (I → K) → Prop} {x : I → K} (hC : C x) (hx : Occurs op x) :
    eigSum op C ≠ ⊥ := fun h => hx (eq_bot_iff.2 ((eigAt_le_eigSum hC).trans h.le))

theorem eigSum_ne_top [FiniteDimensional K V] (hc : PairComm op) {C : (I → K) → Prop} {x : I → K}
    (hC : ¬ C x) (hx : Occurs op x) : eigSum op C ≠ ⊤ := by
  intro h
  have hd : Disjoint (eigSum op C) (eigSum op fun x => ¬ C x) := disjoint_eigSum hc fun x h h' => h' h
  rw [h, top_disjoint] at hd
  exact eigSum_ne_bot (C := fun x => ¬ C x) hC hx hd

theorem eigAt_le_comap {g : End K V} (hg : ∀ i, Commute (op i) g) (x : I → K) :
    eigAt op x ≤ (eigAt op x).comap g := by
  intro v hv
  rw [Submodule.mem_comap, eigAt, Submodule.mem_iInf]
  intro i
  exact mapsTo_maxGenEigenspace_of_comm (hg i) (x i) (eigAt_le op x i hv)

theorem eigSum_le_comap {g : End K V} (hg : ∀ i, Commute (op i) g) (C : (I → K) → Prop) :
    eigSum op C ≤ (eigSum op C).comap g :=
  iSup₂_le fun x hx => (eigAt_le_comap hg x).trans (Submodule.comap_mono (eigAt_le_eigSum hx))

def eigProj [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op) (C : (I → K) → Prop) :
    End K V :=
  (eigSum op C).subtype ∘ₗ Submodule.projectionOnto _ _ (isCompl_eigSum hc hs C)

theorem eigProj_apply_mem [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) (v : V) : eigProj hc hs C v ∈ eigSum op C :=
  (Submodule.projectionOnto _ _ (isCompl_eigSum hc hs C) v).2

theorem eigProj_apply_of_mem [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    {C : (I → K) → Prop} {v : V} (hv : v ∈ eigSum op C) : eigProj hc hs C v = v := by
  have := Submodule.projectionOnto_apply_left (isCompl_eigSum hc hs C) ⟨v, hv⟩
  simp only [eigProj, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [this]

theorem eigProj_apply_of_mem_not [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    {C : (I → K) → Prop} {v : V} (hv : v ∈ eigSum op fun x => ¬ C x) : eigProj hc hs C v = 0 := by
  have := (Submodule.projectionOnto_apply_eq_zero_iff (isCompl_eigSum hc hs C)).2 hv
  simp only [eigProj, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [this]; rfl

theorem sub_eigProj_mem [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) (v : V) : v - eigProj hc hs C v ∈ eigSum op fun x => ¬ C x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
  rw [map_add, eigProj_apply_of_mem hc hs ha, eigProj_apply_of_mem_not hc hs hb, add_zero,
    add_sub_cancel_left]
  exact hb

theorem range_eigProj [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) : LinearMap.range (eigProj hc hs C) = eigSum op C := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩; exact eigProj_apply_mem hc hs C v
  · intro v hv; exact ⟨v, eigProj_apply_of_mem hc hs hv⟩

theorem ker_eigProj [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) : LinearMap.ker (eigProj hc hs C) = eigSum op fun x => ¬ C x := by
  apply le_antisymm
  · intro v hv
    have := sub_eigProj_mem hc hs C v
    rwa [LinearMap.mem_ker.1 hv, sub_zero] at this
  · intro v hv; exact eigProj_apply_of_mem_not hc hs hv

theorem commute_eigProj [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → K) → Prop) {g : End K V} (hg : ∀ i, Commute (op i) g) : Commute (eigProj hc hs C) g := by
  ext v
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
  simp only [Module.End.mul_apply, map_add]
  rw [eigProj_apply_of_mem hc hs ha, eigProj_apply_of_mem_not hc hs hb,
    eigProj_apply_of_mem hc hs (eigSum_le_comap hg C ha),
    eigProj_apply_of_mem_not hc hs (eigSum_le_comap hg _ hb), map_zero]

end Eig

section Cov

variable {O K V I : Type} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

abbrev hAlg (O : Type) {K V I : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (op : I → End K V) : Subalgebra O (End K V) :=
  Algebra.adjoin O (Set.range op)

def hGen (O : Type) {K V I : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (op : I → End K V) (i : I) : hAlg O op :=
  ⟨op i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

variable {op : I → End K V}

def sysOf (ψ : hAlg O op →ₐ[O] O) : I → K := fun i => pt ψ (hGen O op i)

theorem PairComm.range (hc : PairComm op) : ∀ a ∈ Set.range op, ∀ b ∈ Set.range op, Commute a b := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact hc i j

theorem commute_hAlg (hc : PairComm op) {a b : End K V} (ha : a ∈ hAlg O op) (hb : b ∈ hAlg O op) :
    Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b' hb' =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun a' ha' => hc.range b' hb' a' ha').symm

theorem pt_algebraMap (ψ : hAlg O op →ₐ[O] O) (r : O) (h : algebraMap O (End K V) r ∈ hAlg O op) :
    pt ψ ⟨algebraMap O (End K V) r, h⟩ = algebraMap O K r := by
  have e : (⟨algebraMap O (End K V) r, h⟩ : hAlg O op) = algebraMap O (hAlg O op) r :=
    Subtype.ext (Subalgebra.coe_algebraMap _ r).symm
  rw [e, pt, AlgHom.commutes]
  rfl

theorem W_pt_eq_eigAt (hc : PairComm op) (ψ : hAlg O op →ₐ[O] O) :
    W (hAlg O op) (pt ψ) = eigAt op (sysOf ψ) := by
  apply le_antisymm
  · exact le_iInf fun i => W_le _ (pt ψ) (hGen O op i)
  · intro v hv
    rw [W, Submodule.mem_iInf]
    rintro ⟨t, ht⟩
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact eigAt_le op (sysOf ψ) i hv
    | algebraMap r =>
      rw [pt_algebraMap]
      change v ∈ (algebraMap O (End K V) r).maxGenEigenspace _
      rw [algebraMap_end_eq, maxGen_smul_one]
      exact Submodule.mem_top
    | add x y hx hy ihx ihy =>
      have e : pt ψ ⟨x + y, add_mem hx hy⟩ = pt ψ ⟨x, hx⟩ + pt ψ ⟨y, hy⟩ := by
        rw [show (⟨x + y, add_mem hx hy⟩ : hAlg O op) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl]
        simp only [pt, map_add]
      rw [e]
      exact mem_maxGen_add (commute_hAlg hc hx hy) ihx ihy
    | mul x y hx hy ihx ihy =>
      have e : pt ψ ⟨x * y, mul_mem hx hy⟩ = pt ψ ⟨x, hx⟩ * pt ψ ⟨y, hy⟩ := by
        rw [show (⟨x * y, mul_mem hx hy⟩ : hAlg O op) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl]
        simp only [pt, map_mul]
      rw [e]
      exact mem_maxGen_mul (commute_hAlg hc hx hy) ihx ihy

theorem exists_le_maxGen (hc : PairComm op) (x : I → K) (t : hAlg O op) :
    ∃ μ, eigAt op x ≤ (t : End K V).maxGenEigenspace μ := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨x i, eigAt_le op x i⟩
  | algebraMap r =>
    refine ⟨algebraMap O K r, ?_⟩
    change _ ≤ (algebraMap O (End K V) r).maxGenEigenspace _
    rw [algebraMap_end_eq, maxGen_smul_one]
    exact le_top
  | add a b ha hb iha ihb =>
    obtain ⟨α, hα⟩ := iha
    obtain ⟨β, hβ⟩ := ihb
    exact ⟨α + β, fun v hv => mem_maxGen_add (commute_hAlg hc ha hb) (hα hv) (hβ hv)⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨α, hα⟩ := iha
    obtain ⟨β, hβ⟩ := ihb
    exact ⟨α * β, fun v hv => mem_maxGen_mul (commute_hAlg hc ha hb) (hα hv) (hβ hv)⟩

variable [IsLocalRing O]

theorem exists_pt_of_occurs (hc : PairComm op)
    (hint : ∀ i μ, (op i).maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (hinj : Function.Injective (algebraMap O K)) {x : I → K} (hx : Occurs op x) :
    ∃ ψ : hAlg O op →ₐ[O] O, sysOf ψ = x := by
  choose χ hχ using exists_le_maxGen (O := O) hc x
  have hW : W (hAlg O op) χ ≠ ⊥ := fun h => hx (eq_bot_iff.2 ((le_iInf hχ).trans h.le))
  obtain ⟨ψ, hψ⟩ := exists_pt hc.range
    (by rintro _ ⟨i, rfl⟩ μ h; exact hint i μ h) hinj hW
  refine ⟨ψ, funext fun i => ?_⟩
  rw [sysOf, hψ]
  exact (eq_of_occurs_of_le hx (hχ (hGen O op i))).symm

theorem eigenSum_eq_iSup_weightSpaces (hc : PairComm op)
    (hint : ∀ i μ, (op i).maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (hinj : Function.Injective (algebraMap O K)) (C : (I → K) → Prop) :
    eigSum op C = ⨆ (ψ : hAlg O op →ₐ[O] O) (_ : C (sysOf ψ)), W (hAlg O op) (pt ψ) := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    by_cases h0 : eigAt op x = ⊥
    · rw [h0]; exact bot_le
    · obtain ⟨ψ, rfl⟩ := exists_pt_of_occurs hc hint hinj h0
      rw [← W_pt_eq_eigAt hc]
      exact le_iSup₂_of_le (f := fun (ψ : hAlg O op →ₐ[O] O) (_ : C (sysOf ψ)) => W (hAlg O op) (pt ψ))
        ψ hx le_rfl
  · refine iSup₂_le fun ψ hψ => ?_
    rw [W_pt_eq_eigAt hc]
    exact eigAt_le_eigSum hψ

theorem part_eq_eigSum (hc : PairComm op) (𝔪 : Ideal (hAlg O op)) :
    part (hAlg O op) 𝔪 = eigSum op fun x => ∃ ψ : hAlg O op →ₐ[O] O, sysOf ψ = x ∧ cls ψ = 𝔪 := by
  apply le_antisymm
  · refine iSup₂_le fun ψ hψ => ?_
    rw [W_pt_eq_eigAt hc]
    exact eigAt_le_eigSum ⟨ψ, rfl, hψ⟩
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨ψ, rfl, hψ⟩ := hx
    rw [← W_pt_eq_eigAt hc]
    exact le_iSup₂_of_le (f := fun (ψ : hAlg O op →ₐ[O] O) (_ : cls ψ = 𝔪) => W (hAlg O op) (pt ψ))
      ψ hψ le_rfl

theorem off_eq_eigSum (hc : PairComm op) (𝔪 : Ideal (hAlg O op)) :
    off (hAlg O op) 𝔪 = eigSum op fun x => ∃ ψ : hAlg O op →ₐ[O] O, sysOf ψ = x ∧ cls ψ ≠ 𝔪 := by
  apply le_antisymm
  · refine iSup₂_le fun ψ hψ => ?_
    rw [W_pt_eq_eigAt hc]
    exact eigAt_le_eigSum ⟨ψ, rfl, hψ⟩
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨ψ, rfl, hψ⟩ := hx
    rw [← W_pt_eq_eigAt hc]
    exact le_iSup₂_of_le (f := fun (ψ : hAlg O op →ₐ[O] O) (_ : cls ψ ≠ 𝔪) => W (hAlg O op) (pt ψ))
      ψ hψ le_rfl

end Cov

section BaseChange

open TensorProduct

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
variable (L : Type) [Field L] [Algebra K L]

def opL (op : I → End K V) (i : I) : End L (L ⊗[K] V) := (op i).baseChange L

def eigSumOver (op : I → End K V) (C : (I → L) → Prop) : Submodule K V :=
  ((eigSum (opL L op) C).restrictScalars K).comap (TensorProduct.mk K L V 1)

def Descends (op : I → End K V) (C : (I → L) → Prop) : Prop :=
  (eigSumOver L op C).baseChange L = eigSum (opL L op) C

variable {L} {op : I → End K V}

theorem mem_eigSumOver {C : (I → L) → Prop} {v : V} :
    v ∈ eigSumOver L op C ↔ (1 : L) ⊗ₜ[K] v ∈ eigSum (opL L op) C := Iff.rfl

theorem PairComm.opL (hc : PairComm op) : PairComm (opL L op) := by
  intro i j
  have h := hc i j
  unfold Commute SemiconjBy at h ⊢
  simp only [Formalism.L2.Col.opL, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp] at h ⊢
  rw [h]

theorem pow_sub_tmul (f : End K V) (a : K) (k : ℕ) (v : V) :
    ((f.baseChange L - algebraMap K L a • (1 : End L (L ⊗[K] V))) ^ k) ((1 : L) ⊗ₜ[K] v) =
      (1 : L) ⊗ₜ[K] (((f - a • (1 : End K V)) ^ k) v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply,
      Module.End.one_apply, TensorProduct.tmul_sub, TensorProduct.tmul_smul]
    rw [algebraMap_smul]

theorem tmul_mem_eigAt {x : I → K} {v : V} (hv : v ∈ eigAt op x) :
    (1 : L) ⊗ₜ[K] v ∈ eigAt (opL L op) (fun i => algebraMap K L (x i)) := by
  rw [eigAt, Submodule.mem_iInf]
  intro i
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).1 (eigAt_le op x i hv)
  rw [mem_maxGenEigenspace]
  exact ⟨k, by rw [Formalism.L2.Col.opL, pow_sub_tmul, hk, TensorProduct.tmul_zero]⟩

theorem eigSum_le_eigSumOver (C : (I → L) → Prop) :
    eigSum op (fun x => C fun i => algebraMap K L (x i)) ≤ eigSumOver L op C :=
  iSup₂_le fun _ hx _ hv => mem_eigSumOver.2 (eigAt_le_eigSum hx (tmul_mem_eigAt hv))

theorem tmul_one_injective : Function.Injective (fun v : V => (1 : L) ⊗ₜ[K] v) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) V

theorem eigSumOver_eq_eigSum [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → L) → Prop) :
    eigSumOver L op C = eigSum op (fun x => C fun i => algebraMap K L (x i)) := by
  apply le_antisymm _ (eigSum_le_eigSumOver C)
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_eigSum hc hs (fun x => C fun i => algebraMap K L (x i))).sup_eq_top ▸
      (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
  have h1 : (1 : L) ⊗ₜ[K] b ∈ eigSum (opL L op) C := by
    have := (eigSumOver L op C).sub_mem hv (eigSum_le_eigSumOver C ha)
    rwa [add_sub_cancel_left] at this
  have h2 : (1 : L) ⊗ₜ[K] b ∈ eigSum (opL L op) fun y => ¬ C y :=
    eigSum_le_eigSumOver (fun y => ¬ C y) hb
  have h0 := (disjoint_eigSum (hc.opL (L := L)) (C := C) (C' := fun y => ¬ C y)
    fun _ h h' => h' h).le_bot ⟨h1, h2⟩
  have hb0 : b = 0 := tmul_one_injective (L := L) (by
    simp only [TensorProduct.tmul_zero]; exact (Submodule.mem_bot L).1 h0)
  rw [hb0, add_zero]
  exact ha

theorem baseChange_le_of_le_eigSumOver {C : (I → L) → Prop} {p : Submodule K V}
    (h : p ≤ eigSumOver L op C) : p.baseChange L ≤ eigSum (opL L op) C := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  exact h hv

theorem baseChange_sup_eq_top {p p' : Submodule K V} (h : p ⊔ p' = ⊤) :
    p.baseChange L ⊔ p'.baseChange L = ⊤ := by
  rw [eq_top_iff, ← Submodule.baseChange_top, ← h, Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (Submodule.tmul_mem_baseChange_of_mem 1 ha))
    (Submodule.mem_sup_right (Submodule.tmul_mem_baseChange_of_mem 1 hb))

theorem descends_of_split [FiniteDimensional K V] (hc : PairComm op) (hs : SplitOver op)
    (C : (I → L) → Prop) : Descends L op C := by
  apply le_antisymm (baseChange_le_of_le_eigSumOver le_rfl)
  have hA := baseChange_le_of_le_eigSumOver (L := L) (op := op) (C := C) le_rfl
  have hB := baseChange_le_of_le_eigSumOver (L := L) (op := op) (C := fun y => ¬ C y) le_rfl
  have htop : (eigSumOver L op C).baseChange L ⊔ (eigSumOver L op fun y => ¬ C y).baseChange L = ⊤ := by
    rw [eigSumOver_eq_eigSum hc hs, eigSumOver_eq_eigSum hc hs]
    exact baseChange_sup_eq_top (isCompl_eigSum hc hs _).sup_eq_top
  have hd : Disjoint (eigSum (opL L op) C) ((eigSumOver L op fun y => ¬ C y).baseChange L) :=
    (disjoint_eigSum (hc.opL (L := L)) (C := C) (C' := fun y => ¬ C y) fun _ h h' => h' h).mono_right hB
  calc eigSum (opL L op) C = ((eigSumOver L op C).baseChange L ⊔
        (eigSumOver L op fun y => ¬ C y).baseChange L) ⊓ eigSum (opL L op) C := by
        rw [htop, top_inf_eq]
    _ = (eigSumOver L op C).baseChange L := by
        rw [sup_inf_assoc_of_le _ hA, hd.symm.eq_bot, sup_bot_eq]
    _ ≤ _ := le_rfl

end BaseChange

section Basis

variable {K V I J : Type} [Field K] [AddCommGroup V] [Module K V] {op : I → End K V}

theorem pairComm_of_basis (b : Basis J K V) (e : J → I → K) (h : ∀ i j, op i (b j) = e j i • b j) :
    PairComm op := by
  intro i i'
  refine b.ext fun j => ?_
  simp only [Module.End.mul_apply, h, map_smul]
  rw [smul_comm]

theorem splitOver_of_basis (b : Basis J K V) (e : J → I → K) (h : ∀ i j, op i (b j) = e j i • b j) :
    SplitOver op := by
  intro i
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.mem_iSup_of_mem (e j i) ?_
  rw [mem_maxGenEigenspace]
  exact ⟨1, by simp [h i j]⟩

theorem span_le_eigSum (b : Basis J K V) (e : J → I → K)
    (h : ∀ i j, op i (b j) = e j i • b j) (C : (I → K) → Prop) :
    Submodule.span K (b '' {j | C (e j)}) ≤ eigSum op C := by
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact eigAt_le_eigSum (C := C) (x := e j) hj (mem_eigAt_of_forall_apply fun i => h i j)

theorem span_sup_span (b : Basis J K V) (e : J → I → K) (C : (I → K) → Prop) :
    Submodule.span K (b '' {j | C (e j)}) ⊔ Submodule.span K (b '' {j | ¬ C (e j)}) = ⊤ := by
  rw [← Submodule.span_union, ← Set.image_union, eq_top_iff, ← b.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j, em _, rfl⟩

theorem eigSum_eq_span_of_basis [FiniteDimensional K V] (b : Basis J K V) (e : J → I → K)
    (h : ∀ i j, op i (b j) = e j i • b j) (C : (I → K) → Prop) :
    eigSum op C = Submodule.span K (b '' {j | C (e j)}) := by
  have hc := pairComm_of_basis b e h
  have hd : Disjoint (eigSum op C) (Submodule.span K (b '' {j | ¬ C (e j)})) :=
    (disjoint_eigSum hc (C := C) (C' := fun y => ¬ C y) fun _ h h' => h' h).mono_right
      (span_le_eigSum b e h fun y => ¬ C y)
  apply le_antisymm _ (span_le_eigSum b e h C)
  have e1 : eigSum op C = (Submodule.span K (b '' {j | C (e j)}) ⊔
        Submodule.span K (b '' {j | ¬ C (e j)})) ⊓ eigSum op C := by
    rw [span_sup_span b e C, top_inf_eq]
  rw [e1, sup_inf_assoc_of_le _ (span_le_eigSum b e h C), hd.symm.eq_bot, sup_bot_eq]
end Basis

section Poly

open Polynomial

variable {L : Type} [Field L]

def heckePolyOf (n q : ℕ) (a : ℕ → L) : L[X] :=
  ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * (q : L) ^ (i * (i - 1) / 2) * a i) * X ^ i

def blockPoly (ν : L) (q t : ℕ) : L[X] :=
  ∏ c ∈ Finset.range t, (1 - C (ν * (q : L) ^ c) * X)

def gaussBin (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, i + 1 => gaussBin q n i + q ^ (i + 1) * gaussBin q n (i + 1)

theorem gaussBin_eq_zero (q : ℕ) {n i : ℕ} (h : n < i) : gaussBin q n i = 0 := by
  induction n generalizing i with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [gaussBin]
  | succ n ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [gaussBin, ih (by omega), ih (by omega)]
    simp

theorem blockPoly_succ' (ν : L) (q t : ℕ) :
    blockPoly ν q (t + 1) = (1 - C ν * X) * blockPoly (ν * q) q t := by
  rw [blockPoly, Finset.prod_range_succ', blockPoly, mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_succ']
    ring_nf

theorem heckePolyOf_gaussBin (q n : ℕ) (ν : L) :
    heckePolyOf n q (fun i => ν ^ i * (gaussBin q n i : L)) = blockPoly ν q n := by
  induction n generalizing ν with
  | zero => simp [heckePolyOf, blockPoly, gaussBin]
  | succ n ih =>
    rw [blockPoly_succ', ← ih]
    let T : ℕ → L[X] := fun i =>
      C ((-1) ^ i * (q : L) ^ (i * (i - 1) / 2) * ((ν * q) ^ i * (gaussBin q n i : L))) * X ^ i
    have hS : heckePolyOf n q (fun i => (ν * q) ^ i * (gaussBin q n i : L)) =
        ∑ i ∈ Finset.range (n + 1), T i := rfl
    have hlast : T (n + 1) = 0 := by simp [T, gaussBin_eq_zero q (Nat.lt_succ_self n)]
    have step : ∀ i, C ((-1) ^ (i + 1) * (q : L) ^ ((i + 1) * (i + 1 - 1) / 2) *
        (ν ^ (i + 1) * (gaussBin q (n + 1) (i + 1) : L))) * X ^ (i + 1) =
        T (i + 1) - C ν * X * T i := by
      intro i
      simp only [T]
      rw [Nat.triangle_succ, gaussBin]
      push_cast
      simp only [map_mul, map_add, map_pow, map_neg, map_one]
      ring
    have h0 : C ((-1) ^ 0 * (q : L) ^ (0 * (0 - 1) / 2) * (ν ^ 0 * (gaussBin q (n + 1) 0 : L))) * X ^ 0 =
        T 0 := by simp [T, gaussBin]
    have h1 : ∑ i ∈ Finset.range (n + 1), T (i + 1) + T 0 = ∑ i ∈ Finset.range (n + 1), T i := by
      rw [← Finset.sum_range_succ' T (n + 1), Finset.sum_range_succ, hlast, add_zero]
    rw [hS]
    simp only [heckePolyOf]
    rw [Finset.sum_range_succ', h0, Finset.sum_congr rfl (fun i _ => step i), Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    linear_combination h1

theorem map_heckePolyOf {L' : Type} [Field L'] (φ : L →+* L') (n q : ℕ) (a : ℕ → L) :
    (heckePolyOf n q a).map φ = heckePolyOf n q fun i => φ (a i) := by
  simp [heckePolyOf, Polynomial.map_sum]

theorem map_blockPoly {L' : Type} [Field L'] (φ : L →+* L') (ν : L) (q t : ℕ) :
    (blockPoly ν q t).map φ = blockPoly (φ ν) q t := by
  simp [blockPoly, Polynomial.map_prod]

variable {Pl : Type}

def heckePoly (n : ℕ) (q : Pl → ℕ) (x : Pl × ℕ → L) (P : Pl) : L[X] :=
  heckePolyOf n (q P) fun i => x (P, i)

def HasBlocks (n : ℕ) (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → L)) (x : Pl × ℕ → L) : Prop :=
  ∀ P, (bl.map fun ν => blockPoly (ν P) (q P) t).prod ∣ heckePoly n q x P

structure BlockOk (t : ℕ) (bl : List (Pl → L)) : Prop where
  one_le : 1 ≤ t
  ne_nil : bl ≠ []
  ne_zero : ∀ ν ∈ bl, ∀ P, ν P ≠ 0

theorem HasBlocks.of_nil (n : ℕ) (q : Pl → ℕ) (t : ℕ) (x : Pl × ℕ → L) : HasBlocks n q t [] x :=
  fun _ => by simp

theorem HasBlocks.of_len_zero (n : ℕ) (q : Pl → ℕ) (bl : List (Pl → L)) (x : Pl × ℕ → L) :
    HasBlocks n q 0 bl x := fun P => by
  have : (bl.map fun ν => blockPoly (ν P) (q P) 0) = bl.map fun _ => (1 : L[X]) := by
    simp [blockPoly]
  rw [this]
  simp

theorem blockPoly_zero_val (q t : ℕ) : blockPoly (0 : L) q t = 1 := by
  simp [blockPoly]

theorem blockPoly_eval_inv {ν : L} (hν : ν ≠ 0) (q : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    (blockPoly ν q t).eval ν⁻¹ = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [blockPoly_succ']
  simp [hν]

theorem HasBlocks.heckePoly_ne_one {n : ℕ} {q : Pl → ℕ} {t : ℕ} {bl : List (Pl → L)} {x : Pl × ℕ → L}
    (hb : BlockOk t bl) (h : HasBlocks n q t bl x) (P : Pl) : heckePoly n q x P ≠ 1 := by
  intro h1
  obtain ⟨ν, bl', rfl⟩ := List.exists_cons_of_ne_nil hb.ne_nil
  have hd := h P
  rw [h1, List.map_cons, List.prod_cons] at hd
  have h2 := Polynomial.eval_dvd (x := (ν P)⁻¹) ((Dvd.intro _ rfl).trans hd)
  rw [blockPoly_eval_inv (hb.ne_zero ν (List.mem_cons_self) P) (q P) hb.one_le, eval_one, zero_dvd_iff] at h2
  exact one_ne_zero h2

theorem hasBlocks_map {L' : Type} [Field L'] (φ : L →+* L') (n : ℕ) (q : Pl → ℕ) (t : ℕ)
    (bl : List (Pl → L)) (x : Pl × ℕ → L) :
    HasBlocks n q t (bl.map fun ν P => φ (ν P)) (fun i => φ (x i)) ↔ HasBlocks n q t bl x := by
  refine forall_congr' fun P => ?_
  simp only [heckePoly]
  rw [← Polynomial.map_dvd_map' φ, map_heckePolyOf, Polynomial.map_list_prod, List.map_map, List.map_map]
  simp only [Function.comp_def, map_blockPoly]

def firstValA {K Pl : Type} [Field K] (muV etaV : Pl → Kˣ) (q : Pl → ℕ) (r : ℕ) (P : Pl) : K :=
  ((muV P)⁻¹ : Kˣ) * (etaV P : K) * (q P : K) ^ ((r + 1) / 2)

def firstValB {K Pl : Type} [Field K] (muV : Pl → Kˣ) (q : Pl → ℕ) (r m t : ℕ) (P : Pl) : K :=
  (muV P : K) * (q P : K) ^ ((r + (m - 1) * t) / 2)

theorem firstValA_ne_zero {K Pl : Type} [Field K] [CharZero K] (muV etaV : Pl → Kˣ) {q : Pl → ℕ} (r : ℕ) {P : Pl}
    (hq : q P ≠ 0) : firstValA muV etaV q r P ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem firstValB_ne_zero {K Pl : Type} [Field K] [CharZero K] (muV : Pl → Kˣ) {q : Pl → ℕ} (r m t : ℕ) {P : Pl}
    (hq : q P ≠ 0) : firstValB muV q r m t P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem blockOk_firstValA {K Pl : Type} [Field K] [CharZero K] (muV etaV : Pl → Kˣ) {q : Pl → ℕ} (r : ℕ) {t : ℕ}
    (ht : 1 ≤ t) (hq : ∀ P, q P ≠ 0) : BlockOk t [fun P => firstValA muV etaV q r P] :=
  ⟨ht, List.cons_ne_nil _ _, fun ν hν P => by
    rw [List.mem_singleton] at hν
    rw [hν]
    exact firstValA_ne_zero muV etaV r (hq P)⟩

theorem blockOk_firstValB {K Pl : Type} [Field K] [CharZero K] {m : ℕ} (muV : Fin m → Pl → Kˣ) {q : Pl → ℕ}
    (r : ℕ) {t : ℕ} (ht : 1 ≤ t) (hm : 1 ≤ m) (hq : ∀ P, q P ≠ 0) :
    BlockOk t (List.ofFn fun j : Fin m => fun P => firstValB (muV j) q r m t P) :=
  ⟨ht, fun h => by
    have h1 := congrArg List.length h
    rw [List.length_ofFn, List.length_nil] at h1
    omega, fun ν hν P => by
    rw [List.mem_ofFn] at hν
    obtain ⟨j, rfl⟩ := hν
    exact firstValB_ne_zero (muV j) r m t (hq P)⟩

end Poly

section Block

variable {K V Pl : Type} [Field K] [AddCommGroup V] [Module K V]

def blockSum (n : ℕ) (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → K)) (op : Pl × ℕ → End K V) : Submodule K V :=
  eigSum op (HasBlocks n q t bl)

def blockSumOver (L : Type) [Field L] [Algebra K L] (n : ℕ) (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → K))
    (op : Pl × ℕ → End K V) : Submodule K V :=
  eigSumOver L op (HasBlocks n q t (bl.map fun ν P => algebraMap K L (ν P)))

theorem blockSumOver_eq_blockSum [FiniteDimensional K V] (L : Type) [Field L] [Algebra K L] (n : ℕ)
    (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → K)) {op : Pl × ℕ → End K V} (hc : PairComm op)
    (hs : SplitOver op) : blockSumOver L n q t bl op = blockSum n q t bl op := by
  rw [blockSumOver, eigSumOver_eq_eigSum hc hs, blockSum]
  exact eigSum_congr fun x _ => hasBlocks_map (algebraMap K L) n q t bl x

theorem HasBlocks.map_of_fixed {L : Type} [Field L] (φ : L →+* L) {n : ℕ} {q : Pl → ℕ} {t : ℕ}
    {bl : List (Pl → L)} {x : Pl × ℕ → L} (hfix : ∀ ν ∈ bl, ∀ P, φ (ν P) = ν P)
    (h : HasBlocks n q t bl x) : HasBlocks n q t bl fun i => φ (x i) := by
  have e : (bl.map fun ν P => φ (ν P)) = bl := by
    conv_rhs => rw [← List.map_id bl]
    exact List.map_congr_left fun ν hν => funext fun P => hfix ν hν P
  have h2 := (hasBlocks_map φ n q t bl x).2 h
  rwa [e] at h2

theorem HasBlocks.galois {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) {n : ℕ} {q : Pl → ℕ}
    {t : ℕ} {bl : List (Pl → K)} {x : Pl × ℕ → L}
    (h : HasBlocks n q t (bl.map fun ν P => algebraMap K L (ν P)) x) :
    HasBlocks n q t (bl.map fun ν P => algebraMap K L (ν P)) fun i => σ (x i) := by
  refine HasBlocks.map_of_fixed (σ : L →+* L) ?_ h
  intro ν hν P
  obtain ⟨ν', _, rfl⟩ := List.mem_map.1 hν
  exact σ.commutes (ν' P)
end Block

section Example

open Polynomial

def exSys : Fin 2 → Unit × ℕ → ℚ
  | 0 => fun x => (gaussBin 2 2 x.2 : ℚ)
  | 1 => fun x => if x.2 = 0 ∨ x.2 = 2 then 1 else 0

def exOp (x : Unit × ℕ) : End ℚ (Fin 2 → ℚ) := LinearMap.pi fun j => exSys j x • LinearMap.proj j

theorem exOp_apply (x : Unit × ℕ) (j : Fin 2) :
    exOp x (Pi.basisFun ℚ (Fin 2) j) = exSys j x • Pi.basisFun ℚ (Fin 2) j := by
  funext k
  simp only [exOp, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, Pi.basisFun_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : k = j
  · rw [h]
  · simp [h]

theorem ex_has : HasBlocks 2 (fun _ : Unit => 2) 2 [fun _ => (1 : ℚ)] (exSys 0) := by
  intro P
  have h := heckePolyOf_gaussBin (L := ℚ) 2 2 1
  simp only [one_pow, one_mul] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, heckePoly, exSys]
  rw [h]

theorem ex_has_not : ¬ HasBlocks 2 (fun _ : Unit => 2) 2 [fun _ => (1 : ℚ)] (exSys 1) := by
  intro h
  have h1 := h ()
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
  have h2 := Polynomial.eval_dvd (x := (1 : ℚ)) h1
  have e1 : (blockPoly (1 : ℚ) 2 2).eval 1 = 0 := by simp [blockPoly, Finset.prod_range_succ]
  have e2 : (heckePoly 2 (fun _ : Unit => 2) (exSys 1) ()).eval 1 = 3 := by
    simp [heckePoly, heckePolyOf, exSys, Finset.sum_range_succ]
    norm_num
  rw [e1, e2, zero_dvd_iff] at h2
  norm_num at h2

theorem ex_blockSum : blockSum 2 (fun _ : Unit => 2) 2 [fun _ => (1 : ℚ)] exOp =
    Submodule.span ℚ {Pi.basisFun ℚ (Fin 2) 0} := by
  rw [blockSum, eigSum_eq_span_of_basis (Pi.basisFun ℚ (Fin 2)) exSys fun i j => exOp_apply i j]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases j
    · rfl
    · exact absurd hj ex_has_not
  · rintro rfl
    exact ⟨0, ex_has, rfl⟩

theorem ex_finrank : finrank ℚ (blockSum 2 (fun _ : Unit => 2) 2 [fun _ => (1 : ℚ)] exOp) = 1 := by
  rw [ex_blockSum]
  exact finrank_span_singleton ((Pi.basisFun ℚ (Fin 2)).ne_zero 0)

end Example

section Nbr

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def IsHeckeNbr (P : Ideal (𝓞 E)) (i : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  P • N' ≤ N ∧ conjIdeal (K := E) P • N ≤ N' ∧
    Nonempty ((N ⧸ (N' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ conjIdeal (K := E) P))

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.heckeSet (P : Ideal (𝓞 E)) (i : ℕ) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | IsHeckeNbr P i d.1.N d'.1.N ∧ d'.1.f = d.1.f ∧ d'.1.be = d.1.be}

open Classical in

def DecoSet.heckeNb (P : Ideal (𝓞 E)) (i : ℕ) (d : DecoSet E n ST SG) : Finset (DecoSet E n ST SG) :=
  if h : (d.heckeSet P i).Finite then h.toFinset else ∅

def quotMapEquiv {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (g : W ≃ₗ[R] W)
    (A B : Submodule R W) :
    (B ⧸ (A ⊓ B).comap B.subtype) ≃ₗ[R]
      ((B.map (g : W →ₗ[R] W)) ⧸ (A.map (g : W →ₗ[R] W) ⊓ B.map (g : W →ₗ[R] W)).comap
        (B.map (g : W →ₗ[R] W)).subtype) :=
  Submodule.Quotient.equiv _ _ (g.submoduleMap B) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf,
      Subtype.exists]
    constructor
    · rintro ⟨x, hxB, ⟨hxA, _⟩, hxy⟩
      have e : g x = y := congrArg Subtype.val hxy
      exact ⟨⟨x, hxA, e⟩, hy⟩
    · rintro ⟨⟨x, hxA, hx⟩, _⟩
      obtain ⟨x', hx'B, hx'⟩ := hy
      have e : x = x' := g.injective (hx.trans hx'.symm)
      exact ⟨x, e ▸ hx'B, ⟨hxA, e ▸ hx'B⟩, Subtype.ext hx⟩)

theorem IsHeckeNbr.gmap {P : Ideal (𝓞 E)} {i : ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsHeckeNbr P i N N') (g : Sp E n ≃ₗ[E] Sp E n) : IsHeckeNbr P i (gmap g N) (gmap g N') := by
  obtain ⟨h1, h2, ⟨e⟩⟩ := h
  refine ⟨?_, ?_, ⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N' N).symm.trans e⟩⟩
  · unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_smul'']
    exact Submodule.map_mono h1
  · unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_smul'']
    exact Submodule.map_mono h2

end Nbr

section NbrAct

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.smul_mem_heckeSet {P : Ideal (𝓞 E)} {i : ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} (h : e ∈ d.heckeSet P i) : a • e ∈ (a • d).heckeSet P i := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h1.gmap _
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h2]
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h3]

theorem DecoSet.smul_mem_heckeSet_iff {P : Ideal (𝓞 E)} {i : ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} : a • e ∈ (a • d).heckeSet P i ↔ e ∈ d.heckeSet P i := by
  refine ⟨fun h => ?_, DecoSet.smul_mem_heckeSet a⟩
  have := DecoSet.smul_mem_heckeSet a⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem DecoSet.heckeSet_smul (P : Ideal (𝓞 E)) (i : ℕ) (a : UF E n × GLG E n SG)
    (d : DecoSet E n ST SG) : (a • d).heckeSet P i = (fun e => a • e) '' d.heckeSet P i := by
  ext e
  constructor
  · intro h
    refine ⟨a⁻¹ • e, ?_, smul_inv_smul a e⟩
    rw [← DecoSet.smul_mem_heckeSet_iff a, smul_inv_smul]
    exact h
  · rintro ⟨e', h, rfl⟩
    exact DecoSet.smul_mem_heckeSet a h

theorem DecoSet.smul_mem_heckeNb_iff {P : Ideal (𝓞 E)} {i : ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} : a • e ∈ (a • d).heckeNb P i ↔ e ∈ d.heckeNb P i := by
  have hfin : ((a • d).heckeSet P i).Finite ↔ (d.heckeSet P i).Finite := by
    rw [DecoSet.heckeSet_smul]
    exact Set.finite_image_iff (MulAction.injective a).injOn
  unfold DecoSet.heckeNb
  by_cases h : (d.heckeSet P i).Finite
  · rw [dif_pos h, dif_pos (hfin.2 h), Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact DecoSet.smul_mem_heckeSet_iff a
  · rw [dif_neg h, dif_neg (fun h' => h (hfin.1 h'))]
    simp

end NbrAct

section HeckeD

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

structure DecoPts (S : GSD K) (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) where

  pts : S.D ≃ DecoSet E n ST SG

  hom : S.G →* UF E n × GLG E n SG
  pts_smul : ∀ (g : S.G) (d : S.D), pts (g • d) = hom g • pts d

variable {S : GSD K}

def DecoPts.nb (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (d : S.D) : Finset S.D :=
  ((c.pts d).heckeNb P i).map c.pts.symm.toEmbedding

theorem DecoPts.mem_nb (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (d e : S.D) :
    e ∈ c.nb P i d ↔ c.pts e ∈ (c.pts d).heckeNb P i := by
  unfold DecoPts.nb
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

def heckeD (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) : LocOp S S :=
  LocOp.ofNbr (MonoidHom.id S.G) (c.nb P i) LinearMap.id
    (by
      intro g d' d
      rw [c.mem_nb, c.mem_nb, MonoidHom.id_apply, c.pts_smul, c.pts_smul]
      exact DecoSet.smul_mem_heckeNb_iff (c.hom g))
    (by intro g x; rfl)

theorem heckeD_op_apply (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeD c P i).op φ : S.EqFun) : S.D → S.V) d = ∑ e ∈ c.nb P i d, (φ : S.D → S.V) e :=
  LocOp.ofNbr_op_apply _ _ _ _ _ φ d

def SplitOff (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {P : HeightOneSpectrum (𝓞 E) // conjIdeal (K := E) P.asIdeal ≠ P.asIdeal ∧ P ∉ S0 ∧
    ∀ Q ∈ S0, Q.asIdeal ≠ conjIdeal (K := E) P.asIdeal}

def SplitOff.q {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)

abbrev LevOff (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  SplitOff (S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))))

def heckeFam (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    LevOff ST SG S0 × ℕ → End K S.EqFun := fun x => (heckeD c x.1.1.asIdeal x.2).op

def heckeAlgC (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Subalgebra K (End K S.EqFun) :=
  hAlg K (heckeFam c S0)

def blockSumC (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (t : ℕ)
    (bl : List (LevOff ST SG S0 → K)) (_hb : BlockOk t bl) : Submodule K S.EqFun :=
  blockSum n SplitOff.q t bl (heckeFam c S0)

def blockSumCOver (L : Type) [Field L] [Algebra K L] (c : DecoPts S E n ST SG)
    (S0 : Set (HeightOneSpectrum (𝓞 E))) (t : ℕ) (bl : List (LevOff ST SG S0 → K)) (_hb : BlockOk t bl) :
    Submodule K S.EqFun :=
  blockSumOver L n SplitOff.q t bl (heckeFam c S0)

end HeckeD

section NbrLemmas

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Pointwise

theorem finite_between {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (A B : Submodule R W)
    (hfin : Finite (B ⧸ A.comap B.subtype)) : {M : Submodule R W | A ≤ M ∧ M ≤ B}.Finite := by
  have : Finite (Submodule R (B ⧸ A.comap B.subtype)) :=
    Finite.of_injective (fun q => (q : Set (B ⧸ A.comap B.subtype))) SetLike.coe_injective
  have key : ∀ M, A ≤ M → M ≤ B →
      (((M.comap B.subtype).map (A.comap B.subtype).mkQ).comap (A.comap B.subtype).mkQ).map B.subtype = M := by
    intro M h1 h2
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1), Submodule.map_comap_subtype,
      inf_eq_right.2 h2]
  refine Set.Finite.of_injOn (f := fun M => (M.comap B.subtype).map (A.comap B.subtype).mkQ)
    (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_ Set.finite_univ
  intro M hM M' hM' h
  rw [← key M hM.1 hM.2, ← key M' hM'.1 hM'.2]
  exact congrArg (fun q => (q.comap (A.comap B.subtype).mkQ).map B.subtype) h

variable {E : Type} [Field E] [NumberField E]

theorem finite_quot_smul {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (N : Submodule (𝓞 E) W) (hN : N.FG)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Finite (N ⧸ (I • N).comap N.subtype) := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have : Module.Finite ℤ (N ⧸ (I • N).comap N.subtype) := Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro x
  have hm : (Ideal.absNorm I : ℤ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact hI
  refine ⟨⟨(Ideal.absNorm I : ℤ), mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Ideal.absNorm I : ℤ) • (Submodule.Quotient.mk y : N ⧸ (I • N).comap N.subtype) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  have e : N.subtype ((Ideal.absNorm I : ℤ) • y) = ((Ideal.absNorm I : ℕ) : 𝓞 E) • (y : W) := by
    simp [Nat.cast_smul_eq_nsmul]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.absNorm_mem I) y.2

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.heckeSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (hP' : conjIdeal (K := E) P ≠ ⊥) (i : ℕ)
    (d : DecoSet E n ST SG) : (d.heckeSet P i).Finite := by
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hI : Ideal.span {a} * conjIdeal (K := E) P ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hP'⟩
  have hfin := finite_between ((Ideal.span {a} * conjIdeal (K := E) P) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet E n ST SG => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨⟨h1, h2, _⟩, _, _⟩ := he
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h2
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem P).2 haP) le_rfl).trans h1
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_heckeNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (hP' : conjIdeal (K := E) P ≠ ⊥) (i : ℕ)
    (d e : DecoSet E n ST SG) : e ∈ d.heckeNb P i ↔ e ∈ d.heckeSet P i := by
  unfold DecoSet.heckeNb
  rw [dif_pos (DecoSet.heckeSet_finite hP hP' i d), Set.Finite.mem_toFinset]

theorem DecoSet.heckeSet_zero (P : Ideal (𝓞 E)) (d : DecoSet E n ST SG) : d.heckeSet P 0 = {d} := by
  ext e
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, _, ⟨φ⟩⟩, hf, hbe⟩
    have hsub : Subsingleton (d.1.N ⧸ (e.1.N ⊓ d.1.N).comap d.1.N.subtype) := φ.toEquiv.subsingleton
    have htop := Submodule.Quotient.subsingleton_iff.1 hsub
    have hge : d.1.N ≤ e.1.N := by
      intro x hx
      have : (⟨x, hx⟩ : d.1.N) ∈ (e.1.N ⊓ d.1.N).comap d.1.N.subtype := htop ▸ Submodule.mem_top
      exact this.1
    have hle : e.1.N ≤ d.1.N := by
      have h1 := dual_anti hge
      rwa [d.2.uni, e.2.uni] at h1
    exact Subtype.ext (Deco.ext (le_antisymm hle hge) hf hbe)
  · rintro rfl
    refine ⟨⟨Submodule.smul_le_right, Submodule.smul_le_right, ?_⟩, rfl, rfl⟩
    have htop : (e.1.N ⊓ e.1.N).comap e.1.N.subtype = ⊤ := by
      rw [inf_idem, Submodule.comap_subtype_self]
    have : Subsingleton (e.1.N ⧸ (e.1.N ⊓ e.1.N).comap e.1.N.subtype) :=
      Submodule.Quotient.subsingleton_iff.2 htop
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩

end NbrLemmas

section Exist

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem glue_inf {I J : Ideal (𝓞 E)} (hJI : ∀ p ∈ J, cO E p ∈ I) (hcop : ∃ e ∈ I, ∃ e' ∈ J, e + e' = 1)
    {N B : Submodule (𝓞 E) (Sp E n)} (hN : IsUnimodular (hStd E n) N) (hBN : B ≤ N) (hIN : I • N ≤ B) :
    (B ⊔ I • dual (hStd E n) B) ⊓ N = B := by
  apply le_antisymm
  · rintro y ⟨hy', hyN⟩
    obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 hy'
    have hzN : z ∈ N := by
      have := N.sub_mem hyN (hBN hb)
      rwa [add_sub_cancel_left] at this
    obtain ⟨e, he, e', he', hee⟩ := hcop
    have hz1 : e • z ∈ B := hIN (Submodule.smul_mem_smul he hzN)
    have hz2 : e' • z ∈ B := by
      refine hIN ?_
      refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun a b ha hb => ?_)
      · rw [smul_comm]
        exact Submodule.smul_mem_smul hr (conj_smul_dual_mem hN hIN (hJI e' he') hu)
      · rw [smul_add]
        exact add_mem ha hb
    have e1 : z = e • z + e' • z := by rw [← add_smul, hee, one_smul]
    rw [e1]
    exact B.add_mem hb (B.add_mem hz1 hz2)
  · exact le_inf le_sup_left hBN

theorem exists_heckeNbr_ker {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) {i : ℕ}
    (φ : N →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal)) (hφ : Function.Surjective φ) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      IsHeckeNbr P.asIdeal i N N' ∧
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → SameAt Q N N') ∧
      N' ⊓ N = (LinearMap.ker φ).map N.subtype := by
  have hIJ : ∀ p ∈ (conjPrime₂ P).asIdeal, cO E p ∈ P.asIdeal := fun p hp => hp
  have hJI : ∀ p ∈ P.asIdeal, cO E p ∈ (conjPrime₂ P).asIdeal := fun p hp => by
    rw [mem_conjP, cO_cO]
    exact hp
  have hcop := exists_coprime hne
  set B : Submodule (𝓞 E) (Sp E n) := (LinearMap.ker φ).map N.subtype with hB
  have hBN : B ≤ N := Submodule.map_subtype_le _ _
  have hIN : (conjPrime₂ P).asIdeal • N ≤ B := by
    rw [Submodule.smul_le]
    intro r hr x hx
    refine ⟨r • ⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_smul]
    funext k
    rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
    rfl
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (conjPrime₂ P).ne_bot
  have hBl : Submodule.IsLattice E B :=
    lattice_of_smul hlat hlat hBN hp0 fun x hx => hIN (Submodule.smul_mem_smul hp hx)
  obtain ⟨hl', hu'⟩ := glue_unimodular hIJ hJI hcop huni hBl hBN hIN
  have h1 : P.asIdeal • (B ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) B) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    rw [smul_add]
    exact N.add_mem (N.smul_mem r (hBN hb))
      (conj_smul_dual_mem huni hIN (hJI r hr) (Submodule.smul_le_right hz))
  have h2 : (conjPrime₂ P).asIdeal • N ≤ B ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) B := hIN.trans le_sup_left
  refine ⟨B ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) B, hl', hu', ?_, ?_, glue_inf hJI hcop huni hBN hIN⟩
  · unfold IsHeckeNbr
    rw [conjIdeal_asIdeal]
    refine ⟨h1, h2, ?_⟩
    have hk : ((B ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) B) ⊓ N).comap N.subtype = LinearMap.ker φ := by
      rw [glue_inf hJI hcop huni hBN hIN, hB,
        Submodule.comap_map_eq_of_injective N.injective_subtype]
    exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (φ.quotKerEquivOfSurjective hφ)⟩
  · intro Q hQ hQ'
    obtain ⟨a, haP, haQ⟩ := exists_mem_notMem (Ne.symm hQ)
    obtain ⟨a', haP', haQ'⟩ := exists_mem_notMem (Ne.symm hQ')
    exact ⟨a, haQ, a', haQ', fun x hx => h1 (Submodule.smul_mem_smul haP hx),
      fun x hx => h2 (Submodule.smul_mem_smul haP' hx)⟩

theorem exists_heckeNbr {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) {i : ℕ}
    (φ : N →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal)) (hφ : Function.Surjective φ) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      IsHeckeNbr P.asIdeal i N N' ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → SameAt Q N N' := by
  obtain ⟨N', h1, h2, h3, h4, _⟩ := exists_heckeNbr_ker hlat huni P hne φ hφ
  exact ⟨N', h1, h2, h3, h4⟩

theorem IsHeckeNbr.eq_glue {N N' : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (huni' : IsUnimodular (hStd E n) N')
    (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) {i : ℕ} (h : IsHeckeNbr P.asIdeal i N N') :
    N' = (N' ⊓ N) ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) (N' ⊓ N) := by
  obtain ⟨h1, h2, _⟩ := h
  rw [conjIdeal_asIdeal] at h2
  have hIJ : ∀ p ∈ (conjPrime₂ P).asIdeal, cO E p ∈ P.asIdeal := fun p hp => hp
  have hJI : ∀ p ∈ P.asIdeal, cO E p ∈ (conjPrime₂ P).asIdeal := fun p hp => by
    rw [mem_conjP, cO_cO]
    exact hp
  have hIN : (conjPrime₂ P).asIdeal • N ≤ N' ⊓ N := le_inf h2 Submodule.smul_le_right
  have hIN' : P.asIdeal • N' ≤ N' ⊓ N := le_inf Submodule.smul_le_right h1
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (conjPrime₂ P).ne_bot
  have hBl : Submodule.IsLattice E (N' ⊓ N) :=
    lattice_of_smul hlat hlat inf_le_right hp0 fun x hx => hIN (Submodule.smul_mem_smul hp hx)
  obtain ⟨_, hu⟩ := glue_unimodular hIJ hJI (exists_coprime hne) huni hBl inf_le_right hIN
  have hle : (N' ⊓ N) ⊔ (conjPrime₂ P).asIdeal • dual (hStd E n) (N' ⊓ N) ≤ N' := by
    refine sup_le inf_le_left (Submodule.smul_le.2 fun r hr u hu' => ?_)
    exact conj_smul_dual_mem huni' hIN' (hIJ r hr) hu'
  refine le_antisymm ?_ hle
  have h3 := dual_anti hle
  rwa [show dual (hStd E n) N' = N' from huni', show dual (hStd E n) _ = _ from hu] at h3

theorem Deco.Ok.replN {d : Deco E n ST SG} (hd : d.Ok) {N' : Submodule (𝓞 E) (Sp E n)}
    (hlat : Submodule.IsLattice E N') (huni : IsUnimodular (hStd E n) N')
    (hST : ∀ Q : ST, SameAt Q.1 d.N N') (hSG : ∀ w : SG, SameAt w.1 d.N N') :
    ({ N := N', f := d.f, be := d.be } : Deco E n ST SG).Ok := by
  have hat : ∀ Q : HeightOneSpectrum (𝓞 E),
      ({ N := N', f := d.f, be := d.be } : Deco E n ST SG).at Q = localization₂ Q.asIdeal N' := fun _ => rfl
  refine ⟨hlat, huni, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q x hx y hy
    rw [hat, (hST Q).localization_eq] at hx hy
    exact hd.f_add Q x hx y hy
  · intro Q a x hx
    rw [hat, (hST Q).localization_eq] at hx
    exact hd.f_smul Q a x hx
  · intro Q x hx
    rw [hat, (hST Q).localization_eq] at hx
    exact hd.f_off Q x hx
  · intro Q
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hST Q
    obtain ⟨x, hx, hne⟩ := hd.f_ne Q
    refine ⟨a' • x, h2 x hx, ?_⟩
    change d.f Q (a' • x) ≠ 0
    rw [hd.f_smul Q a' x (le_locP _ _ hx)]
    exact mul_ne_zero (mk_ne_zero ha') hne
  · intro w x hx y hy
    rw [hat, (hSG w).localization_eq] at hx hy
    exact hd.be_add w x hx y hy
  · intro w a x hx
    rw [hat, (hSG w).localization_eq] at hx
    exact hd.be_smul w a x hx
  · intro w x hx
    rw [hat, (hSG w).localization_eq] at hx
    exact hd.be_off w x hx
  · intro w c
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hSG w
    have := w.1.isMaximal
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero ha')
    obtain ⟨x, hx, hc⟩ := hd.be_surj w (b • c)
    refine ⟨a' • x, h2 x hx, ?_⟩
    change d.be w (a' • x) = c
    rw [hd.be_smul w a' x (le_locP _ _ hx), hc, smul_smul, hb, one_smul]
  · intro w x hx h0
    have hsame := hSG w
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hSG w
    replace hx : x ∈ N' := hx
    replace h0 : d.be w x = 0 := h0
    have hxl : x ∈ d.at w.1 := by
      rw [Deco.at, ← hsame.localization_eq]
      exact le_locP _ _ hx
    have h3 : a • x ∈ w.1.asIdeal • d.N := by
      apply hd.be_ker w _ (h1 x hx)
      rw [hd.be_smul w a x hxl, h0, smul_zero]
    have h4 : a' • (a • x) ∈ w.1.asIdeal • N' := by
      refine Submodule.smul_induction_on h3 (fun r hr y hy => ?_) (fun y z hy hz => ?_)
      · rw [smul_comm]
        exact Submodule.smul_mem_smul hr (h2 y hy)
      · rw [smul_add]
        exact Submodule.add_mem _ hy hz
    rw [← mul_smul] at h4
    exact mem_smul_of_loc hx (fun hm => (w.1.isPrime.mem_or_mem hm).elim ha' ha) h4

theorem DecoSet.heckeSet_nonempty_of_surj (d : DecoSet E n ST SG) (P : HeightOneSpectrum (𝓞 E))
    (hne : conjPrime₂ P ≠ P) (hST : ∀ Q : ST, Q.1 ≠ P ∧ Q.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P)
    {i : ℕ} (φ : d.1.N →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal)) (hφ : Function.Surjective φ) :
    (d.heckeSet P.asIdeal i).Nonempty := by
  obtain ⟨N', hl, hu, hnb, hsame⟩ := exists_heckeNbr d.2.lat d.2.uni P hne φ hφ
  exact ⟨⟨{ N := N', f := d.1.f, be := d.1.be },
    d.2.replN hl hu (fun Q => hsame Q.1 (hST Q).1 (hST Q).2) (fun w => hsame w.1 (hSG w).1 (hSG w).2)⟩,
    hnb, rfl, rfl⟩

theorem intAt_of_mem_stdLat (Q : HeightOneSpectrum (𝓞 E)) {x : Sp E n} (hx : x ∈ stdLat E n) (j : Fin n) :
    IntAt Q (x j) := by
  obtain ⟨r, hr⟩ := (mem_stdLat x).1 hx j
  rw [← hr]
  exact IntAt.coe Q r

def redMap (Q : HeightOneSpectrum (𝓞 E)) {n i : ℕ} (h : i ≤ n) :
    stdLat E n →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ Q.asIdeal) where
  toFun x k := redP Q (x.1 (Fin.castLE h k))
  map_add' x y := funext fun k =>
    reduction_add (intAt_of_mem_stdLat Q x.2 _) (intAt_of_mem_stdLat Q y.2 _)
  map_smul' c x := funext fun k => by
    change redP Q (c • x.1 (Fin.castLE h k)) = c • redP Q (x.1 (Fin.castLE h k))
    rw [redP_osmul c (intAt_of_mem_stdLat Q x.2 _), Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

theorem redMap_surjective (Q : HeightOneSpectrum (𝓞 E)) {n i : ℕ} (h : i ≤ n) :
    Function.Surjective (redMap (E := E) Q h) := by
  intro c
  choose r hr using fun k => Ideal.Quotient.mk_surjective (c k)
  refine ⟨⟨fun j => if hj : j.1 < i then algebraMap (𝓞 E) E (r ⟨j.1, hj⟩) else 0, ?_⟩, ?_⟩
  · rw [mem_stdLat]
    intro j
    by_cases hj : j.1 < i
    · exact ⟨r ⟨j.1, hj⟩, by rw [dif_pos hj]⟩
    · exact ⟨0, by rw [dif_neg hj, map_zero]⟩
  · funext k
    change redP Q (if hj : (Fin.castLE h k).1 < i then algebraMap (𝓞 E) E (r ⟨(Fin.castLE h k).1, hj⟩) else 0) = c k
    rw [dif_pos (by simp), reduction_coe]
    exact hr k

theorem DecoSet.heckeSet_base_nonempty [NeZero n] (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    (hST : ∀ Q : ST, Q.1 ≠ P ∧ Q.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) {i : ℕ}
    (hi : i ≤ n) : ((DecoSet.base E n ST SG).heckeSet P.asIdeal i).Nonempty :=
  DecoSet.heckeSet_nonempty_of_surj (DecoSet.base E n ST SG) P hne hST hSG (redMap (conjPrime₂ P) hi)
    (redMap_surjective (conjPrime₂ P) hi)

end Exist

section Fam

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem conjIdeal_ne_bot {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) : conjIdeal (K := E) P ≠ ⊥ := by
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  intro h
  have h1 : cO E a ∈ conjIdeal (K := E) P := by
    rw [mem_conjIdeal, cO_cO]
    exact haP
  rw [h, Ideal.mem_bot] at h1
  apply ha
  rw [← cO_cO (E := E) a, h1, map_zero]

theorem DecoPts.mem_nb_iff (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (d e : S.D) :
    e ∈ c.nb P.asIdeal i d ↔ c.pts e ∈ (c.pts d).heckeSet P.asIdeal i := by
  rw [c.mem_nb, DecoSet.mem_heckeNb P.ne_bot (conjIdeal_ne_bot P.ne_bot)]

theorem heckeFam_zero (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (P : LevOff ST SG S0) :
    heckeFam c S0 (P, 0) = 1 := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
  have h : c.nb P.1.asIdeal 0 d = {d} := by
    ext e
    rw [c.mem_nb_iff, DecoSet.heckeSet_zero, Set.mem_singleton_iff, Finset.mem_singleton,
      c.pts.apply_eq_iff_eq]
  change (((heckeD c P.1.asIdeal 0).op φ : S.EqFun) : S.D → S.V) d = _
  rw [heckeD_op_apply, h, Finset.sum_singleton]
  rfl

def HeckeComm (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  PairComm (heckeFam c S0)

def HeckeFieldsIn (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFam c S0)

def blockProjC [FiniteDimensional K S.EqFun] (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E)))
    (hc : HeckeComm c S0) (hs : HeckeFieldsIn c S0) (t : ℕ) (bl : List (LevOff ST SG S0 → K))
    (_hb : BlockOk t bl) : End K S.EqFun :=
  eigProj hc hs (HasBlocks n SplitOff.q t bl)

theorem range_blockProjC [FiniteDimensional K S.EqFun] (c : DecoPts S E n ST SG)
    (S0 : Set (HeightOneSpectrum (𝓞 E))) (hc : HeckeComm c S0) (hs : HeckeFieldsIn c S0) (t : ℕ)
    (bl : List (LevOff ST SG S0 → K)) (hb : BlockOk t bl) :
    LinearMap.range (blockProjC c S0 hc hs t bl hb) = blockSumC c S0 t bl hb :=
  range_eigProj hc hs _

theorem heckePoly_coeff_zero (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E)))
    {x : LevOff ST SG S0 × ℕ → K} (hx : Occurs (heckeFam c S0) x) (P : LevOff ST SG S0) :
    (heckePoly n SplitOff.q x P).coeff 0 = 1 := by
  have h1 : x (P, 0) = 1 := hx.eq_one (heckeFam_zero c S0 P)
  simp [heckePoly, heckePolyOf, Polynomial.coeff_X_pow, Finset.sum_ite_eq, h1]

end Fam

section Triv

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
  (ST SG : Finset (HeightOneSpectrum (𝓞 E)))

def trivPts : DecoPts (GSD.triv K (UF E n × GLG E n SG) (DecoSet E n ST SG)) E n ST SG where
  pts := Equiv.refl _
  hom := MonoidHom.id _
  pts_smul := fun _ _ => rfl

theorem heckeD_trivOne (P : Ideal (𝓞 E)) (i : ℕ) (d : DecoSet E n ST SG) :
    (((heckeD (trivPts K E n ST SG) P i).op (GSD.trivOne K (UF E n × GLG E n SG) (DecoSet E n ST SG)) :
      (GSD.triv K (UF E n × GLG E n SG) (DecoSet E n ST SG)).EqFun) : DecoSet E n ST SG → K) d =
      (((trivPts K E n ST SG).nb P i d).card : K) := by
  rw [heckeD_op_apply]
  change ∑ _e ∈ (trivPts K E n ST SG).nb P i d, (1 : K) = _
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Triv

section NonZero

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem SplitOff.conjP_ne {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : conjPrime₂ P.1 ≠ P.1 :=
  fun h => P.2.1 (by rw [conjIdeal_asIdeal, h])

theorem SplitOff.ne_of_mem {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ∈ S0) : Q ≠ P.1 ∧ Q ≠ conjPrime₂ P.1 :=
  ⟨fun h => P.2.2.1 (h ▸ hQ), fun h => P.2.2.2 Q hQ (by rw [conjIdeal_asIdeal, h])⟩

theorem LevOff.notMem {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S0 : Set (HeightOneSpectrum (𝓞 E))}
    (P : LevOff ST SG S0) : (P.1 ∉ ST ∧ conjPrime₂ P.1 ∉ ST) ∧ (P.1 ∉ SG ∧ conjPrime₂ P.1 ∉ SG) ∧ (P.1 ∉ S0 ∧ conjPrime₂ P.1 ∉ S0) :=
  ⟨⟨fun h => (SplitOff.ne_of_mem P (Or.inl (Or.inr h))).1 rfl, fun h => (SplitOff.ne_of_mem P (Or.inl (Or.inr h))).2 rfl⟩,
    ⟨fun h => (SplitOff.ne_of_mem P (Or.inr h)).1 rfl, fun h => (SplitOff.ne_of_mem P (Or.inr h)).2 rfl⟩,
    ⟨fun h => (SplitOff.ne_of_mem P (Or.inl (Or.inl h))).1 rfl, fun h => (SplitOff.ne_of_mem P (Or.inl (Or.inl h))).2 rfl⟩⟩

theorem SplitOff.q_ne_zero {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : P.q ≠ 0 := by
  have : Finite (𝓞 E ⧸ P.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.1.ne_bot
  exact Nat.card_pos.ne'

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem heckeFam_triv_ne_zero [NeZero n] (S0 : Set (HeightOneSpectrum (𝓞 E))) (P : LevOff ST SG S0) {i : ℕ}
    (hi : i ≤ n) :
    heckeFam (trivPts K E n ST SG) S0 (P, i) ≠ 0 := by
  intro h
  have h1 := heckeD_trivOne K E n ST SG P.1.asIdeal i (DecoSet.base E n ST SG)
  have h2 : (heckeD (trivPts K E n ST SG) P.1.asIdeal i).op = 0 := h
  rw [h2] at h1
  obtain ⟨e, he⟩ := DecoSet.heckeSet_base_nonempty (ST := ST) (SG := SG) (n := n) P.1 P.conjP_ne
    (fun Q => P.ne_of_mem (Or.inl (Or.inr Q.2))) (fun w => P.ne_of_mem (Or.inr w.2)) hi
  have h3 : e ∈ (trivPts K E n ST SG).nb P.1.asIdeal i (DecoSet.base E n ST SG) :=
    ((trivPts K E n ST SG).mem_nb_iff P.1 i _ e).2 he
  have h4 : (((trivPts K E n ST SG).nb P.1.asIdeal i (DecoSet.base E n ST SG)).card : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem h3)
  exact h4 h1.symm

end NonZero

end Formalism.L2.Col
