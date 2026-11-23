import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittSemisimpleMatrixRepresentationsStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section
namespace GlobalTheory.RedCharpoly

section Transfer
variable {A B M M₁ : Type} [Ring A] [Ring B] [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module B M₁]

def subIso (e : M ≃+ M₁) (h1 : ∀ a : A, ∃ b : B, ∀ x, e (a • x) = b • e x)
    (h2 : ∀ b : B, ∃ a : A, ∀ x, e (a • x) = b • e x) : Submodule A M ≃o Submodule B M₁ where
  toFun p :=
    { carrier := {y | e.symm y ∈ p}
      add_mem' := fun {x y} hx hy => by
        change e.symm (x + y) ∈ p
        rw [map_add]; exact p.add_mem hx hy
      zero_mem' := by
        change e.symm 0 ∈ p
        rw [map_zero]; exact p.zero_mem
      smul_mem' := fun b y hy => by
        obtain ⟨a, ha⟩ := h2 b
        change e.symm (b • y) ∈ p
        have : e.symm (b • y) = a • e.symm y := by
          rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply]
        rw [this]; exact p.smul_mem a hy }
  invFun q :=
    { carrier := {x | e x ∈ q}
      add_mem' := fun {x y} hx hy => by
        change e (x + y) ∈ q
        rw [map_add]; exact q.add_mem hx hy
      zero_mem' := by
        change e 0 ∈ q
        rw [map_zero]; exact q.zero_mem
      smul_mem' := fun a x hx => by
        obtain ⟨b, hb⟩ := h1 a
        change e (a • x) ∈ q
        rw [hb]; exact q.smul_mem b hx }
  left_inv p := by
    ext x
    change e.symm (e x) ∈ p ↔ _
    rw [AddEquiv.symm_apply_apply]
  right_inv q := by
    ext y
    change e (e.symm y) ∈ q ↔ _
    rw [AddEquiv.apply_symm_apply]
  map_rel_iff' {p p'} := by
    constructor
    · intro h x hx
      have : e.symm (e x) ∈ p' := h (show e.symm (e x) ∈ p by rwa [AddEquiv.symm_apply_apply])
      rwa [AddEquiv.symm_apply_apply] at this
    · intro h y hy
      exact h hy

theorem exists_subquot (e : M ≃+ M₁) (p q : Submodule A M) (p₁ q₁ : Submodule B M₁)
    (hp : ∀ y, y ∈ p₁ ↔ e.symm y ∈ p) (hq : ∀ y, y ∈ q₁ ↔ e.symm y ∈ q) :
    ∃ f : (↥p ⧸ q.comap p.subtype) ≃+ (↥p₁ ⧸ q₁.comap p₁.subtype),
      ∀ (a : A) (b : B), (∀ x, e (a • x) = b • e x) → ∀ z, f (a • z) = b • f z := by
  let e' : ↥p ≃+ ↥p₁ :=
    { toFun := fun x => ⟨e x, (hp _).2 (by simp)⟩
      invFun := fun y => ⟨e.symm y, (hp _).1 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by simp }
  refine ⟨QuotientAddGroup.congr (q.comap p.subtype).toAddSubgroup (q₁.comap p₁.subtype).toAddSubgroup e' ?_,
    fun a b hab z => ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ∈ q₁
      rw [hq, AddEquiv.symm_apply_apply]
      exact hx
    · intro hy
      exact ⟨e'.symm y, (hq _).1 hy, e'.apply_symm_apply y⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (e' (a • x)) = Submodule.Quotient.mk (b • e' x)
    congr 1
    exact Subtype.ext (hab x)

variable {N N₁ : Type} [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module B N₁]

theorem sameFactors_transfer (e : M ≃+ M₁) (e' : N ≃+ N₁)
    (h1 : ∀ a : A, ∃ b : B, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h2 : ∀ b : B, ∃ a : A, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h : SameFactors A M N) : SameFactors B M₁ N₁ := by
  obtain ⟨s, t, s0, s1, t0, t1, c, hc⟩ := h
  let o := subIso e (fun a => (h1 a).imp fun _ h => h.1) (fun a => (h2 a).imp fun _ h => h.1)
  let o' := subIso e' (fun a => (h1 a).imp fun _ h => h.2) (fun a => (h2 a).imp fun _ h => h.2)
  let s' : CompositionSeries (Submodule B M₁) :=
    { length := s.length
      toFun := fun i => o (s i)
      step := fun i => (apply_covBy_apply_iff o).mpr (s.step i) }
  let t' : CompositionSeries (Submodule B N₁) :=
    { length := t.length
      toFun := fun i => o' (t i)
      step := fun i => (apply_covBy_apply_iff o').mpr (t.step i) }
  refine ⟨s', t', ?_, ?_, ?_, ?_, c, fun i => ?_⟩
  · change o s.head = ⊥
    rw [s0, map_bot]
  · change o s.last = ⊤
    rw [s1, map_top]
  · change o' t.head = ⊥
    rw [t0, map_bot]
  · change o' t.last = ⊤
    rw [t1, map_top]
  · obtain ⟨g⟩ := hc i
    obtain ⟨f, hf⟩ := exists_subquot e (s i.succ) (s i.castSucc) (o (s i.succ)) (o (s i.castSucc))
      (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    obtain ⟨f', hf'⟩ := exists_subquot e' (t (c i).succ) (t (c i).castSucc) (o' (t (c i).succ))
      (o' (t (c i).castSucc)) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    refine ⟨{ (f.symm.trans g.toAddEquiv).trans f' with map_smul' := fun b y => ?_ }⟩
    obtain ⟨a, ha, ha'⟩ := h2 b
    obtain ⟨z, rfl⟩ := f.surjective y
    change f' (g (f.symm (b • f z))) = b • f' (g (f.symm (f z)))
    rw [← hf a b ha, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, map_smul, hf' a b ha']

theorem sameFactors_iff (e : M ≃+ M₁) (e' : N ≃+ N₁)
    (h1 : ∀ a : A, ∃ b : B, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h2 : ∀ b : B, ∃ a : A, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x) :
    SameFactors A M N ↔ SameFactors B M₁ N₁ := by
  refine ⟨sameFactors_transfer e e' h1 h2, sameFactors_transfer e.symm e'.symm (fun b => ?_) (fun a => ?_)⟩
  · obtain ⟨a, ha, ha'⟩ := h2 b
    exact ⟨a, fun x => by rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply],
      fun x => by rw [AddEquiv.symm_apply_eq, ha', AddEquiv.apply_symm_apply]⟩
  · obtain ⟨b, ha, ha'⟩ := h1 a
    exact ⟨b, fun x => by rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply],
      fun x => by rw [AddEquiv.symm_apply_eq, ha', AddEquiv.apply_symm_apply]⟩

end Transfer

section Reps
variable {O k G : Type} [CommRing O] [CommRing k] [Algebra O k] [Group G]

theorem single_smul_compat {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module k W]
    (π : Representation O G M) (τ : Representation k G W) (e : π.asModule ≃+ τ.asModule)
    (hg : ∀ g (x : M), e (π g x) = τ g (e x))
    (hs : ∀ (a : O) (x : M), e (a • x) = (algebraMap O k a • (show W from e x) : W)) (g : G) (a : O) (x : π.asModule) :
    e ((MonoidAlgebra.single g a : MonoidAlgebra O G) • x) =
      (MonoidAlgebra.single g (algebraMap O k a) : MonoidAlgebra k G) • e x := by
  have h1 : ((MonoidAlgebra.single g a : MonoidAlgebra O G) • x : π.asModule) = (a • π g x : M) := by
    change π.asAlgebraHom (MonoidAlgebra.single g a) x = _
    simp
    rfl
  have h2 : ((MonoidAlgebra.single g (algebraMap O k a) : MonoidAlgebra k G) • e x : τ.asModule) =
      (algebraMap O k a • τ g (e x) : W) := by
    change τ.asAlgebraHom (MonoidAlgebra.single g _) (e x) = _
    simp
    rfl
  rw [h1, h2, hs]
  exact congrArg (fun y : W => algebraMap O k a • y) (hg g x)

theorem sameSS_iff_of_surjective (hk : Function.Surjective (algebraMap O k))
    {M W M' W' : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module k W]
    [AddCommGroup M'] [Module O M'] [AddCommGroup W'] [Module k W']
    (π : Representation O G M) (τ : Representation k G W) (e : M ≃+ W)
    (hg : ∀ g x, e (π g x) = τ g (e x)) (hs : ∀ (a : O) x, e (a • x) = algebraMap O k a • e x)
    (π' : Representation O G M') (τ' : Representation k G W') (e' : M' ≃+ W')
    (hg' : ∀ g x, e' (π' g x) = τ' g (e' x)) (hs' : ∀ (a : O) x, e' (a • x) = algebraMap O k a • e' x) :
    SameSS π π' ↔ SameSS τ τ' := by
  let E : π.asModule ≃+ τ.asModule := e
  let E' : π'.asModule ≃+ τ'.asModule := e'
  refine sameFactors_iff E E' (fun a => ?_) (fun b => ?_)
  · induction a using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun x => by simp, fun x => by simp⟩
    | add a a' ha ha' =>
      obtain ⟨b, h1, h2⟩ := ha
      obtain ⟨b', h3, h4⟩ := ha'
      exact ⟨b + b', fun x => by rw [add_smul, add_smul, map_add, h1, h3],
        fun x => by rw [add_smul, add_smul, map_add, h2, h4]⟩
    | single g a => exact ⟨_, single_smul_compat π τ E hg hs g a, single_smul_compat π' τ' E' hg' hs' g a⟩
  · induction b using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun x => by simp, fun x => by simp⟩
    | add a a' ha ha' =>
      obtain ⟨b, h1, h2⟩ := ha
      obtain ⟨b', h3, h4⟩ := ha'
      exact ⟨b + b', fun x => by rw [add_smul, add_smul, map_add, h1, h3],
        fun x => by rw [add_smul, add_smul, map_add, h2, h4]⟩
    | single g b =>
      obtain ⟨a, rfl⟩ := hk b
      exact ⟨_, single_smul_compat π τ E hg hs g a, single_smul_compat π' τ' E' hg' hs' g a⟩

end Reps

section Field
variable {k G : Type} [Field k] [Group G]

theorem brauerNesbitt : GlobalTheory.ConstituentsCompare.BrauerNesbitt := by
  intro Γ k _ _ a ρ ρ' h h' hc
  obtain ⟨P, hP⟩ := GlobalTheory.T.brauer_nesbitt_semisimple_matrix_representations a ((Units.coeHom _).comp ρ) ((Units.coeHom _).comp ρ')
    (fun W hW => (h W hW).imp fun _ h => ⟨h.2, h.1⟩) (fun W hW => (h' W hW).imp fun _ h => ⟨h.2, h.1⟩) hc
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm

theorem charpoly_eq_cpOn {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    haveI : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
    LinearMap.charpoly (ρ g) = GlobalTheory.ConsCompare.cpOn k (MonoidAlgebra.of k G g) ρ.asModule := by
  unfold GlobalTheory.ConsCompare.cpOn
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]
  rfl

theorem sameSS_iff_charpoly {V W : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W) :
    SameSS ρ σ ↔ ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g) := by
  refine ⟨fun h g => ?_, fun h => GlobalTheory.ConsCompare.sameSS_of_charpoly_eq brauerNesbitt ρ σ h⟩
  haveI : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  haveI : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  rw [charpoly_eq_cpOn, charpoly_eq_cpOn]
  exact GlobalTheory.ConsCompare.cpOn_eq_of_sameFactors _ h

end Field

section Lat
variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  {ρ : Representation LL G V}

theorem charpoly_lattice (L : Lattice (O := O) ρ) [Module.Free O L.T] [Module.Finite O L.T] (g : G) :
    LinearMap.charpoly (ρ g) = (LinearMap.charpoly (latRep L g)).map (algebraMap O LL) := by
  classical
  let b := Module.Free.chooseBasis O L.T
  have hli : LinearIndependent LL (L.T.subtype ∘ b) :=
    (LinearIndependent.iff_fractionRing O LL).mp (b.linearIndependent.map' L.T.subtype L.T.ker_subtype)
  have hsum : ∀ x : L.T, (x : V) = ∑ i, algebraMap O LL (b.repr x i) • (L.T.subtype ∘ b) i := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hsp : ⊤ ≤ Submodule.span LL (Set.range (L.T.subtype ∘ b)) := by
    rw [← L.span, Submodule.span_le]
    intro x hx
    rw [show x = _ from hsum ⟨x, hx⟩]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B := Module.Basis.mk hli hsp
  rw [← LinearMap.charpoly_toMatrix _ B, ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have : ρ g (B j) = ∑ i, algebraMap O LL (b.repr (latRep L g (b j)) i) • B i := by
    simp only [B, Module.Basis.mk_apply]
    exact hsum (latRep L g (b j))
  rw [this, B.repr_sum_self]

end Lat

def bcRep {O G M : Type} (k : Type) [CommRing O] [CommRing k] [Algebra O k] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) : Representation k G (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toMonoidHom.comp π

theorem sameSS_iff_map_charpoly {O k G M M' N N' : Type} [CommRing O] [Nontrivial O] [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) [Group G] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
    [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N']
    (π : Representation O G M) (π' : Representation O G M') (α : Representation O G N)
    (α' : Representation O G N') (e : N ≃ₗ[O] k ⊗[O] M) (e' : N' ≃ₗ[O] k ⊗[O] M')
    (he : ∀ g x, e (α g x) = (π g).baseChange k (e x)) (he' : ∀ g x, e' (α' g x) = (π' g).baseChange k (e' x)) :
    SameSS α α' ↔ ∀ g, (LinearMap.charpoly (π g)).map (algebraMap O k) =
      (LinearMap.charpoly (π' g)).map (algebraMap O k) := by
  refine ((sameSS_iff_of_surjective hk α (bcRep k π) e.toAddEquiv he
    (fun a x => by rw [algebraMap_smul]; exact map_smul e a x) α' (bcRep k π') e'.toAddEquiv he'
    (fun a x => by rw [algebraMap_smul]; exact map_smul e' a x)).trans (sameSS_iff_charpoly _ _)).trans ?_
  refine forall_congr' fun g => ?_
  rw [← LinearMap.charpoly_baseChange, ← LinearMap.charpoly_baseChange]
  rfl

theorem equivQuotTensor_modRep {O G N : Type} [CommRing O] [Group G] [AddCommGroup N] [Module O N]
    (α : Representation O G N) (c : O) (g : G) (x : QuotSMulTop c N) :
    QuotSMulTop.equivQuotTensor c N (modRep α c g x) =
      (α g).baseChange (O ⧸ Ideal.span {c}) (QuotSMulTop.equivQuotTensor c N x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact QuotSMulTop.equivQuotTensor_naturality_mk c (α g) x

theorem sameSS_modRep_iff {O G M M' : Type} [CommRing O] [Nontrivial O] [Group G] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
    (π : Representation O G M) (π' : Representation O G M') (c : O) (hc : (Ideal.span {c}).IsMaximal) :
    SameSS (modRep π c) (modRep π' c) ↔
      ∀ g j, c ∣ (LinearMap.charpoly (π g) - LinearMap.charpoly (π' g)).coeff j := by
  letI := Ideal.Quotient.field (Ideal.span {c})
  refine (sameSS_iff_map_charpoly (k := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective π π' _ _
    (QuotSMulTop.equivQuotTensor c M) (QuotSMulTop.equivQuotTensor c M') (equivQuotTensor_modRep π c)
    (equivQuotTensor_modRep π' c)).trans ?_
  refine forall_congr' fun g => ?_
  rw [← sub_eq_zero, ← Polynomial.map_sub, Polynomial.ext_iff]
  refine forall_congr' fun j => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory.RedCharpoly
end
