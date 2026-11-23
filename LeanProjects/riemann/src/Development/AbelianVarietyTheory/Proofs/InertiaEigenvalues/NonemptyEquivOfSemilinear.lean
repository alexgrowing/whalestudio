import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

section Semi

variable {R R' : Type} [Ring R] [Ring R'] (σ : R →+* R') [RingHomSurjective σ]
variable {M N X Y : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup X] [Module R' X] [AddCommGroup Y] [Module R' Y]

theorem nonempty_equiv_of_semilinear (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (g : N →ₛₗ[σ] Y)
    (hg : Function.Bijective g) (u : M ≃ₗ[R] N) : Nonempty (X ≃ₗ[R'] Y) := by
  let f' : M ≃+ X := AddEquiv.ofBijective f.toAddMonoidHom hf
  let g' : N ≃+ Y := AddEquiv.ofBijective g.toAddMonoidHom hg
  have key : ∀ x, (f'.symm.trans (u.toAddEquiv.trans g')) (f x) = g (u x) := fun x => by
    change g' (u (f'.symm (f' x))) = _
    rw [AddEquiv.symm_apply_apply]; rfl
  refine ⟨{ f'.symm.trans (u.toAddEquiv.trans g') with map_smul' := fun c x => ?_ }⟩
  obtain ⟨c, rfl⟩ := RingHomSurjective.is_surjective (σ := σ) c
  obtain ⟨x, rfl⟩ := hf.2 x
  change (f'.symm.trans (u.toAddEquiv.trans g')) (σ c • f x) = σ c • (f'.symm.trans (u.toAddEquiv.trans g')) (f x)
  rw [← map_smulₛₗ, key, key, map_smul, map_smulₛₗ]

def mapSeries (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (s : CompositionSeries (Submodule R M)) :
    CompositionSeries (Submodule R' X) where
  length := s.length
  toFun := fun i => Submodule.orderIsoMapComapOfBijective f hf (s i)
  step := fun i => (apply_covBy_apply_iff (Submodule.orderIsoMapComapOfBijective f hf)).mpr (s.step i)

theorem exists_factor_map (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (p q : Submodule R M) :
    ∃ u : (↥q ⧸ p.comap q.subtype) →ₛₗ[σ] (↥(q.map f) ⧸ (p.map f).comap (q.map f).subtype),
      Function.Bijective u := by
  let r : ↥q →ₛₗ[σ] ↥(q.map f) := (f.domRestrict q).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  refine ⟨Submodule.mapQ _ _ r fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy, hxy⟩ := (Submodule.Quotient.mk_eq_zero _).1 (show Submodule.Quotient.mk (r x) = 0 from hx)
    rw [Submodule.Quotient.mk_eq_zero]
    have : y = x := hf.1 hxy
    change (x : M) ∈ p
    exact this ▸ hy
  · intro y
    obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

theorem sameFactors_of_semilinear (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (g : N →ₛₗ[σ] Y)
    (hg : Function.Bijective g) (h : SameFactors R M N) : SameFactors R' X Y := by
  obtain ⟨s, t, h1, h2, h3, h4, e, he⟩ := h
  refine ⟨mapSeries σ f hf s, mapSeries σ g hg t, ?_, ?_, ?_, ?_, e, fun i => ?_⟩
  · change Submodule.orderIsoMapComapOfBijective f hf s.head = ⊥
    rw [h1, map_bot]
  · change Submodule.orderIsoMapComapOfBijective f hf s.last = ⊤
    rw [h2, map_top]
  · change Submodule.orderIsoMapComapOfBijective g hg t.head = ⊥
    rw [h3, map_bot]
  · change Submodule.orderIsoMapComapOfBijective g hg t.last = ⊤
    rw [h4, map_top]
  · obtain ⟨u⟩ := he i
    obtain ⟨a, ha⟩ := exists_factor_map σ f hf (s (Fin.castSucc (n := s.length) i)) (s (Fin.succ (n := s.length) i))
    obtain ⟨b, hb⟩ := exists_factor_map σ g hg (t (e i).castSucc) (t (e i).succ)
    exact nonempty_equiv_of_semilinear σ a ha b hb u

end Semi

section Res

variable {O k G : Type} [CommRing O] [Field k] [Algebra O k] [Group G]

def twHom (k : Type) [Field k] [Algebra O k] (θ : G →* Oˣ) : MonoidAlgebra O G →ₐ[O] MonoidAlgebra k G :=
  MonoidAlgebra.lift _ _ _
    { toFun := fun g => MonoidAlgebra.single g (algebraMap O k ((θ g)⁻¹ : Oˣ))
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := fun g h => by simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twHom_single (θ : G →* Oˣ) (g : G) (a : O) :
    twHom k θ (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap O k (a * ((θ g)⁻¹ : Oˣ))) := by
  rw [twHom, MonoidAlgebra.lift_single]
  change a • MonoidAlgebra.single g (algebraMap O k ((θ g)⁻¹ : Oˣ)) = _
  rw [MonoidAlgebra.smul_single, map_mul, Algebra.smul_def]

theorem twHom_surjective (hs : Function.Surjective (algebraMap O k)) (θ : G →* Oˣ) :
    Function.Surjective (twHom k θ) := by
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | single g c =>
    obtain ⟨a, rfl⟩ := hs c
    exact ⟨MonoidAlgebra.single g (a * θ g), by rw [twHom_single]; simp [mul_assoc]⟩

variable {M N X Y : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup X] [Module k X] [Module O X] [IsScalarTower O k X]
  [AddCommGroup Y] [Module k Y] [Module O Y] [IsScalarTower O k Y]

def twSemi (θ : G →* Oˣ) (π : Representation O G M) (α : Representation k G X) (e : M →ₗ[O] X)
    (he : ∀ g x, e (twistRep π θ g x) = α g (e x)) :
    π.asModule →ₛₗ[(twHom k θ : MonoidAlgebra O G →+* MonoidAlgebra k G)] α.asModule where
  toFun x := α.asModuleEquiv.symm (e (π.asModuleEquiv x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    apply α.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | single g c =>
      rw [RingHom.coe_coe, twHom_single, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, LinearMap.smul_apply, ← he, twistRep_apply, algebraMap_smul, map_smul, map_smul,
        smul_smul]
      simp

theorem sameSS_twist_residue (hs : Function.Surjective (algebraMap O k)) (θ : G →* Oˣ)
    {π : Representation O G M} {π' : Representation O G N} {α : Representation k G X} {α' : Representation k G Y}
    (e : M ≃ₗ[O] X) (he : ∀ g x, e (twistRep π θ g x) = α g (e x))
    (e' : N ≃ₗ[O] Y) (he' : ∀ g x, e' (twistRep π' θ g x) = α' g (e' x)) (h : SameSS π π') : SameSS α α' := by
  have : RingHomSurjective (twHom k θ : MonoidAlgebra O G →+* MonoidAlgebra k G) := ⟨twHom_surjective hs θ⟩
  refine sameFactors_of_semilinear _ (twSemi θ π α e.toLinearMap he) ?_ (twSemi θ π' α' e'.toLinearMap he') ?_ h
  · exact α.asModuleEquiv.symm.bijective.comp (e.bijective.comp π.asModuleEquiv.bijective)
  · exact α'.asModuleEquiv.symm.bijective.comp (e'.bijective.comp π'.asModuleEquiv.bijective)

theorem exists_descend {lam : O} (hs : Function.Surjective (algebraMap O k)) (h0 : algebraMap O k lam = 0)
    (q : M →ₗ[O] X) (hq : Function.Surjective q) (hk : KerIs lam q) (f : M →ₗ[O] Y) :
    ∃ a : X →ₗ[k] Y, ∀ x, a (q x) = f x := by
  have hle : LinearMap.ker q ≤ LinearMap.ker f := fun x hx => by
    obtain ⟨y, rfl⟩ := (hk x).1 hx
    rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul k, h0, zero_smul]
  let a : X →ₗ[O] Y := (Submodule.liftQ _ f hle).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  refine ⟨a.extendScalarsOfSurjective hs, fun x => ?_⟩
  change Submodule.liftQ _ f hle ((q.quotKerEquivOfSurjective hq).symm (q x)) = _
  have : (q.quotKerEquivOfSurjective hq).symm (q x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem exists_reduction {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) [Module.Free O M] [Module.Finite O M]
    (π : Representation O G M) : ∃ (A : Ob k G) (q : M →ₗ[O] (Fin A.m → k)), A.m = Module.finrank O M ∧
      Function.Surjective q ∧ KerIs lam q ∧ ∀ g x, q (π g x) = A.ρ g (q x) := by
  have : Nontrivial O := (algebraMap O k).domain_nontrivial
  let b := (Module.finBasis O M).equivFun
  let q : M →ₗ[O] (Fin (Module.finrank O M) → k) := ((Algebra.linearMap O k).compLeft _).comp b.toLinearMap
  have hq' : ∀ x j, q x j = algebraMap O k (b x j) := fun _ _ => rfl
  have hq : Function.Surjective q := fun y => by
    choose x hx using fun j => hs (y j)
    exact ⟨b.symm x, funext fun j => by rw [hq', LinearEquiv.apply_symm_apply, hx]⟩
  have hK : KerIs lam q := fun x => by
    constructor
    · intro h
      choose y hy using fun j => (hk (b x j)).1 (congrFun h j)
      refine ⟨b.symm y, b.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact funext hy
    · rintro ⟨y, rfl⟩
      rw [map_smul, ← algebraMap_smul k, (hk lam).2 dvd_rfl, zero_smul]
  choose a ha using fun g => exists_descend hs ((hk lam).2 dvd_rfl) q hq hK (q.comp (π g))
  refine ⟨⟨_, { toFun := a, map_one' := ?_, map_mul' := fun g h => ?_ }⟩, q, rfl, hq, hK, fun g x => (ha g x).symm⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hq y
    rw [ha]; simp
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hq y
    have ha' : ∀ g x, a g (q x) = q (π g x) := ha
    change a (g * h) (q x) = a g (a h (q x))
    rw [ha', ha', ha', map_mul, Module.End.mul_apply]

end Res

section Fun

variable {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l}

theorem pre_push_sup (F : DFun R n G) (A B C : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (ha : IsHom A C a)
    (hb : IsHom B C b) (hab : Function.Bijective (a.coprod b)) (N : Lats k n A.m) (N' : Lats k n B.m) :
    F.pre A C a (fun i => F.push A C a N i ⊔ F.push B C b N' i) = N := by
  let e := LinearEquiv.ofBijective (a.coprod b) hab
  let p : (Fin C.m → k) →ₗ[k] (Fin A.m → k) := (LinearMap.fst k _ _).comp e.symm.toLinearMap
  have hp : ∀ x y, p (a x + b y) = x := fun x y => congrArg Prod.fst (e.symm_apply_apply (x, y))
  have hpH : IsHom C A p := fun g z => by
    obtain ⟨⟨x, y⟩, rfl⟩ := hab.2 z
    rw [LinearMap.coprod_apply, map_add, ← ha, ← hb, hp, hp]
  have h1 : p ∘ₗ a = LinearMap.id := LinearMap.ext fun x => by simpa using hp x 0
  have h2 : p ∘ₗ b = (0 : k) • (p ∘ₗ b) := LinearMap.ext fun y => by simpa using hp 0 y
  have hpb : IsHom B A (p ∘ₗ b) := fun g x => by
    change p (b _) = A.ρ g (p (b x))
    rw [hb, hpH]
  have h3 : ∀ i x, F.map C A p i (F.map A C a i x) = x := fun i x => by
    rw [← LinearMap.comp_apply, ← F.map_comp A C A a p hA hC hA ha hpH, h1, F.map_id A hA, LinearMap.id_apply]
  have h4 : ∀ i x, F.map C A p i (F.map B C b i x) = 0 := fun i x => by
    rw [← LinearMap.comp_apply, ← F.map_comp B C A b p hB hC hA hb hpH, h2, F.map_smul B A _ _ hB hA hpb, zero_smul]
  funext i
  ext x
  constructor
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, -, rfl⟩, h⟩ := Submodule.mem_sup.1 (show F.map A C a i x ∈ _ from hx)
    have h' := congrArg (F.map C A p i) h
    change F.map C A p i (F.map A C a i y + F.map B C b i z) = _ at h'
    rw [map_add, h3, h3, h4, add_zero] at h'
    exact h' ▸ hy
  · intro hx
    exact Submodule.mem_sup_left ⟨x, hx, rfl⟩

def IsTrace (F : DFun R n G) (A : Ob k G) (N : Lats k n A.m) (C : Ob k G) (L : Lats k n C.m) : Prop :=
  ∃ a, IsHom A C a ∧ Function.Injective a ∧ N = F.pre A C a L

theorem IsTrace.refl (F : DFun R n G) (A : Ob k G) (hA : F.Obj A) (N : Lats k n A.m) : IsTrace F A N A N :=
  ⟨LinearMap.id, fun _ _ => rfl, Function.injective_id, by
    funext i; ext x
    change _ ↔ F.map A A LinearMap.id i x ∈ N i
    rw [F.map_id A hA, LinearMap.id_apply]⟩

theorem IsTrace.trans {F : DFun R n G} {A B C : Ob k G} (hC : F.Obj C) {N : Lats k n A.m} {M : Lats k n B.m}
    {L : Lats k n C.m} (h : IsTrace F A N B M) (h' : IsTrace F B M C L) : IsTrace F A N C L := by
  obtain ⟨a, ha, hi, rfl⟩ := h
  obtain ⟨b, hb, hj, rfl⟩ := h'
  have hB := F.obj_sub B C b hb hj hC
  have hA := F.obj_sub A B a ha hi hB
  refine ⟨b ∘ₗ a, fun g x => by rw [LinearMap.comp_apply, LinearMap.comp_apply, ha, hb], hj.comp hi, ?_⟩
  funext i; ext x
  change _ ↔ F.map A C (b ∘ₗ a) i x ∈ L i
  rw [F.map_comp A B C a b hA hB hC ha hb]
  rfl

theorem isTrace_sum (F : DFun R n G) (A B C : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hC : F.Obj C) (ha : IsHom A C a)
    (hb : IsHom B C b) (hab : Function.Bijective (a.coprod b)) (N : Lats k n A.m) (N' : Lats k n B.m) :
    IsTrace F A N C (fun i => F.push A C a N i ⊔ F.push B C b N' i) ∧
      IsTrace F B N' C (fun i => F.push A C a N i ⊔ F.push B C b N' i) := by
  have hi : Function.Injective a := fun x y h => congrArg Prod.fst (hab.1 (a₁ := (x, 0)) (a₂ := (y, 0)) (by simpa))
  have hj : Function.Injective b := fun x y h => congrArg Prod.snd (hab.1 (a₁ := (0, x)) (a₂ := (0, y)) (by simpa))
  have hA := F.obj_sub A C a ha hi hC
  have hB := F.obj_sub B C b hb hj hC
  refine ⟨⟨a, ha, hi, (pre_push_sup F A B C a b hA hB hC ha hb hab N N').symm⟩, b, hb, hj, ?_⟩
  have hba : Function.Bijective (b.coprod a) := by
    have : ⇑(b.coprod a) = (a.coprod b) ∘ Prod.swap := funext fun x => by simp [add_comm]
    rw [this]
    exact hab.comp Prod.swap_bijective
  simp only [sup_comm (F.push A C a N _)]
  exact (pre_push_sup F B A C b a hB hA hC hb ha hba N' N).symm

theorem IsTrace.isModel {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A C : Ob k G}
    (hC : F.Obj C) {N : Lats k n A.m} {L : Lats k n C.m} (h : IsTrace F A N C L) (hb : Base C L) :
    IsModel F Base A N := by
  obtain ⟨a, ha, hi, rfl⟩ := h
  refine ⟨C, L, A, a, LinearMap.id, hb, ha, hi, fun _ _ => rfl, Function.surjective_id, ?_⟩
  funext i
  change _ = Submodule.map _ _
  rw [F.map_id A (F.obj_sub A C a ha hi hC)]
  exact (Submodule.map_id _).symm

theorem eq_span_unit [Fact l.Prime] [CharP k l] [NeZero n] (F : DFun R n G) (ψ : G →* kˣ) (hψ : ψ = 1)
    (N : Lats k n 1) (hN : ∀ i, IsLat (N i)) (h : ∀ i, pull ((F.D (chr ψ)).φ i) (N (i - 1)) = sh 0 (N i)) :
    ∀ i, N i = Submodule.span k⟦X⟧ {F.unit i} := by
  subst hψ
  let M : Lats k n 1 := fun i => Submodule.span k⟦X⟧ {F.unit i}
  have hM : ∀ i, IsLat (M i) := fun i => by
    refine ⟨Submodule.fg_span_singleton _, eq_top_iff.2 fun x _ => ?_⟩
    have h1 : F.unit i ∈ Submodule.span k⸨X⸩ (M i : Set (Vc k 1)) :=
      Submodule.subset_span (Submodule.mem_span_singleton_self _)
    have h0 : F.unit i 0 ≠ 0 := fun h0 => F.unit_ne i (funext fun j => by rw [Subsingleton.elim j 0]; exact h0)
    have h2 : x = (x 0 / F.unit i 0) • F.unit i := funext fun j => by
      rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hM' : ∀ i, pull ((F.D (chr 1)).φ i) (M (i - 1)) = M i := fun i => by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨d, hd⟩ := R.φ_int c
      refine Submodule.mem_span_singleton.2 ⟨d, ?_⟩
      rw [← algebraMap_smul k⸨X⸩ c, (F.D (chr 1)).φ_semi i, F.unit_φ, ← algebraMap_smul k⸨X⸩ d]
      exact congrArg (· • F.unit i) hd.symm
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact Submodule.subset_span ⟨_, Submodule.mem_span_singleton_self _, F.unit_φ i⟩
  have c1 : CondAB (F.D (chr 1)).φ (fun _ => 0) (fun _ => ((0 : ℕ) : ℤ) - 0) N := fun i => by
    rw [h i]; simp
  have c2 : CondAB (F.D (chr 1)).φ (fun _ => 0) (fun _ => ((0 : ℕ) : ℤ) - 0) M := fun i => by
    rw [hM' i]; simp [sh_zero_eq]
  intro i
  have hs : sg l (fun _ : ZMod n => 0) i = 0 := by simp [sg]
  have d1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr 1)) (fun _ => 0) (fun _ => 0) N M hN hM c1 c2 i
  have d2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr 1)) (fun _ => 0) (fun _ => 0) M N hM hN c2 c1 i
  rw [hs, Nat.cast_zero, sh_zero_eq] at d1 d2
  exact le_antisymm d1 d2

theorem resCount_nsmul_map (μ : ℕ) (U : Multiset ℤ) (w : ℤ) (x : k) :
    resCount ((μ • U).map (· + -w)) 0 x = μ * resCount U w x := by
  classical
  simp only [resCount, ← Multiset.countP_eq_card_filter, Multiset.countP_map, Multiset.filter_nsmul,
    Multiset.card_nsmul, sub_zero, ← sub_eq_add_neg]

end Fun

section Arith

variable {n r : ℕ} (D : TopData n r)

theorem w_range (i : ZMod n) : 1 ≤ D.w i ∧ D.w i ≤ (D.h i : ℤ) - 1 :=
  D.range i _ (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by have := D.one_le_letterBlockLength; omega⟩)))

theorem eq_of_dvd {l : ℕ} (h1 : D.T1 l) (h3 : D.T3 l) (i : ZMod n) (hi : D.ty i = LType.Bd) (u : ℤ)
    (hu : u ∈ D.Ut i) (a : ℕ) (ha : (a : ℤ) ≤ D.wst i) (hd : (l : ℤ) ∣ (a : ℤ) - (u + -D.w i)) :
    (a : ℤ) = u + -D.w i := by
  have hw := D.lowBd i hi (D.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by have := D.one_le_letterBlockLength; omega⟩)))
  have hl := h1 i
  rw [TopData.wst] at ha
  have low : u ∈ D.lows i + block (D.w i) D.t → (a : ℤ) = u + -D.w i := fun h => by
    have := D.lowBd i hi u h
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; omega)
    omega
  rcases Multiset.mem_add.1 hu with hu | hu
  · rcases Multiset.mem_add.1 hu with hu | hu
    · exact low (Multiset.mem_add.2 (Or.inl hu))
    · refine absurd ?_ (h3 i u hu ((D.h i : ℤ) - D.w i - a) (by omega) (by omega))
      rw [TopData.cloudRes, hi]
      refine (Int.modEq_iff_dvd.2 ?_).symm
      convert hd using 1
      ring
  · exact low (Multiset.mem_add.2 (Or.inr hu))

end Arith

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def piLattice {μ : ℕ} (T : LocLat G Qp LL O) (F : Fin μ → LocLat G Qp LL O) (e : T.V ≃ₗ[LL] (∀ j, (F j).V))
    (he : ∀ g x j, e (T.ρ g x) j = (F j).ρ g (e x j)) :
    {L : Lattice (O := O) T.ρ // ∃ u : ↥L.T ≃ₗ[O] (∀ j, ↥(F j).L.T), ∀ x j, (u x j : (F j).V) = e x j} := by
  let N : Submodule O T.V := (Submodule.pi Set.univ fun j => (F j).L.T).comap (e.restrictScalars O).toLinearMap
  let u : ↥N ≃ₗ[O] (∀ j, ↥(F j).L.T) :=
    { toFun := fun x j => ⟨e x j, x.2 j trivial⟩
      invFun := fun y => ⟨e.symm fun j => y j, fun j _ => by
        change e (e.symm _) j ∈ _
        rw [LinearEquiv.apply_symm_apply]; exact (y j).2⟩
      map_add' := fun x y => funext fun j => Subtype.ext (congrFun (map_add e x.1 y.1) j)
      map_smul' := fun c x => funext fun j => Subtype.ext (congrFun (map_smul (e.restrictScalars O) c x.1) j)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => funext fun j => Subtype.ext (congrFun (e.apply_symm_apply fun j => y j) j) }
  have hfin : ∀ j, Module.Finite O ↥(F j).L.T := fun j => StdAdm.finite_lat (F j)
  have hfree : ∀ j, Module.Free O ↥(F j).L.T := fun j => (F j).L.free
  refine ⟨{ T := N, stable := fun g x hx j _ => ?_, fg := ?_, free := Module.Free.of_equiv u.symm, span := ?_ },
    u, fun _ _ => rfl⟩
  · change e (T.ρ g x) j ∈ _
    rw [he]
    exact (F j).L.stable g _ (hx j trivial)
  · exact Module.Finite.iff_fg.mp (Module.Finite.equiv u.symm)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    rw [← Finset.univ_sum_single y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hy : y j ∈ Submodule.span LL ((F j).L.T : Set (F j).V) := by rw [(F j).L.span]; trivial
    have h1 := Submodule.mem_map_of_mem
      (f := e.symm.toLinearMap.comp (LinearMap.single LL (fun j => (F j).V) j)) hy
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, rfl⟩ i _
    change e (e.symm (Pi.single j a)) i ∈ _
    rw [LinearEquiv.apply_symm_apply]
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact ha
    · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

def piLoc [IsTopologicalRing LL] {μ : ℕ} (F : Fin μ → LocLat G Qp LL O) : LocLat G Qp LL O where
  V := ∀ j, (F j).V
  ρ := piRep fun j => (F j).ρ
  cont := fun x => continuous_pi fun j => (F j).cont (x j)
  L :=
    { T := Submodule.pi Set.univ fun j => (F j).L.T
      stable := fun g x hx j _ => (F j).L.stable g _ (hx j trivial)
      fg := Submodule.fg_pi fun j => (F j).L.fg
      free := by
        have hfree : ∀ j, Module.Free O ↥(F j).L.T := fun j => (F j).L.free
        let u : ↥(Submodule.pi Set.univ fun j => (F j).L.T) ≃ₗ[O] (∀ j, ↥(F j).L.T) :=
          { toFun := fun x j => ⟨x.1 j, x.2 j trivial⟩
            invFun := fun y => ⟨fun j => y j, fun j _ => (y j).2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        exact Module.Free.of_equiv u.symm
      span := by
        rw [eq_top_iff]
        intro y _
        rw [← Finset.univ_sum_single y]
        refine Submodule.sum_mem _ fun j _ => ?_
        have hy : y j ∈ Submodule.span LL ((F j).L.T : Set (F j).V) := by rw [(F j).L.span]; trivial
        have h1 := Submodule.mem_map_of_mem (f := LinearMap.single LL (fun j => (F j).V) j) hy
        rw [Submodule.map_span] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨a, ha, rfl⟩ i _
        change Pi.single (M := fun j => (F j).V) j a i ∈ _
        by_cases h : i = j
        · subst h; rw [Pi.single_eq_same]; exact ha
        · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _ }

variable {k : Type} [Field k] [Algebra O k]

theorem exists_sum_reduction {lam : O} (T T' Z : LocLat G Qp LL O) (u : ↥Z.L.T ≃ₗ[O] (↥T.L.T × ↥T'.L.T))
    (hu : ∀ g x, u (latRep Z.L g x) = (latRep T.L g (u x).1, latRep T'.L g (u x).2))
    (A B : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k))
    (h : Onto T A q) (hk : KerIs lam q) (h' : Onto T' B q') (hk' : KerIs lam q') :
    ∃ (C : Ob k G) (r : ↥Z.L.T →ₗ[O] (Fin C.m → k)) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
      (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), Onto Z C r ∧ KerIs lam r ∧ IsHom A C a ∧ IsHom B C b ∧
      Function.Bijective (a.coprod b) ∧ ∀ z, r z = a (q (u z).1) + b (q' (u z).2) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, (e.restrictScalars O).toLinearMap ∘ₗ (q.prodMap q') ∘ₗ u.toLinearMap,
    e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _,
    ⟨e.surjective.comp ((h.1.prodMap h'.1).comp u.surjective), fun g x => ?_⟩, fun x => ?_, fun g x => ?_,
    fun g x => ?_, ?_, fun z => ?_⟩
  · change e (q (u _).1, q' (u _).2) = C.ρ g (e (q (u x).1, q' (u x).2))
    rw [hu, h.2, h'.2, ← he]
    rfl
  · change e (q (u x).1, q' (u x).2) = 0 ↔ _
    rw [e.map_eq_zero_iff, Prod.mk_eq_zero, hk, hk']
    constructor
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      refine ⟨u.symm (a, b), u.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact Prod.ext ha hb
    · rintro ⟨y, rfl⟩
      rw [map_smul]
      exact ⟨⟨_, rfl⟩, _, rfl⟩
  · change e (A.ρ g x, 0) = C.ρ g (e (x, 0))
    rw [← he]
    exact congrArg e (Prod.ext rfl (map_zero (B.ρ g)).symm)
  · change e (0, B.ρ g x) = C.ρ g (e (0, x))
    rw [← he]
    exact congrArg e (Prod.ext (map_zero (A.ρ g)).symm rfl)
  · have : ⇑((e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)) = e :=
      funext fun x => by simp [← map_add]
    rw [this]
    exact e.bijective
  · change e (q (u z).1, q' (u z).2) = e (q (u z).1, 0) + e (0, q' (u z).2)
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

theorem exists_char_reduction {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (T : LocLat G Qp LL O) (u : O ≃ₗ[O] ↥T.L.T) (χ : G →* Oˣ)
    (hu : ∀ g a, latRep T.L g (u a) = (χ g : O) • u a) (ψ : G →* kˣ) (hψ : ∀ g, (ψ g : k) = algebraMap O k (χ g)) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr ψ) q ∧ KerIs lam q := by
  let q : ↥T.L.T →ₗ[O] (Fin 1 → k) := (LinearMap.pi fun _ => Algebra.linearMap O k) ∘ₗ u.symm.toLinearMap
  have hq : ∀ a j, q (u a) j = algebraMap O k a := fun a j => congrArg (algebraMap O k) (u.symm_apply_apply a)
  refine ⟨q, ⟨fun y => ?_, fun g x => ?_⟩, fun x => ?_⟩
  · obtain ⟨a, ha⟩ := hs (y 0)
    exact ⟨u a, funext fun j => by rw [hq, ha, Subsingleton.elim j 0]⟩
  · obtain ⟨a, rfl⟩ := u.surjective x
    rw [hu, map_smul, ← algebraMap_smul k, ← hψ]
    rfl
  · obtain ⟨a, rfl⟩ := u.surjective x
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := (hk a).1 ((hq a 0).symm.trans (congrFun h 0))
      exact ⟨u b, map_smul u lam b⟩
    · rintro ⟨y, hy⟩
      rw [hy, map_smul, ← algebraMap_smul k, (hk lam).2 dvd_rfl, zero_smul]

theorem kerIs_iff {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {lam : O}
    {q : M →ₗ[O] N} (h : KerIs lam q) (x : M) : q x = 0 ↔ x ∈ lam • (⊤ : Submodule O M) := by
  rw [h x, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, trivial, hy.symm⟩, fun ⟨y, _, hy⟩ => ⟨y, hy.symm⟩⟩

theorem exists_quot_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {lam : O}
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (h : KerIs lam q) :
    ∃ e : QuotSMulTop lam M ≃ₗ[O] N, ∀ x, e (Submodule.Quotient.mk x) = q x := by
  have hker : lam • (⊤ : Submodule O M) = LinearMap.ker q := by
    ext x; rw [LinearMap.mem_ker, kerIs_iff h]
  exact ⟨(Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq), fun _ => rfl⟩

theorem exists_ref_equiv (Γ : GalData G Qp LL O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (A : Ob k G) (q : ↥Γ.T₀.L.T →ₗ[O] (Fin A.m → k))
    (hq : Function.Surjective q) (hK : KerIs Γ.lam q) (hg : ∀ g x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ g x) = A.ρ g (q x))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) (t : ℕ) :
    ∃ e : (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) ≃ₗ[O]
      ((Fin A.m → k) × (Fin t → (Fin 1 → k))),
      ∀ g x, e (twistRep (Γ.refRep t) Γ.χ₁⁻¹ g x) = refSum A ω t g (e x) := by
  obtain ⟨e₀, he₀⟩ := exists_quot_equiv q hq hK
  let q₁ : O →ₗ[O] (Fin 1 → k) := LinearMap.pi fun _ => Algebra.linearMap O k
  have hq₁ : Function.Surjective q₁ := fun y => by
    obtain ⟨a, ha⟩ := hs (y 0)
    exact ⟨a, funext fun j => by rw [Subsingleton.elim j 0]; exact ha⟩
  have hK₁ : KerIs Γ.lam q₁ := fun x =>
    ⟨fun h => (hk x).1 (congrFun h 0), fun h => funext fun _ => (hk x).2 h⟩
  obtain ⟨e₁, he₁⟩ := exists_quot_equiv q₁ hq₁ hK₁
  have hω' : ω = (Units.map (algebraMap O k : O →* k)).comp Γ.ε := MonoidHom.ext fun g => Units.ext (hω g)
  refine ⟨e₀.prodCongr (LinearEquiv.piCongrRight fun _ => e₁), fun g x => Prod.ext ?_ (funext fun c => ?_)⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ x.1
    change e₀ (((Γ.χ₁⁻¹ g : Oˣ) : O) • modRep Γ.W₀ Γ.lam g x.1) = A.ρ g (e₀ x.1)
    rw [← hy, he₀, ← hg]
    exact he₀ _
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.2 c)
    change e₁ (((Γ.χ₁⁻¹ g : Oˣ) : O) • modRep (Γ.Wchi (c.val + 1)) Γ.lam g (x.2 c)) =
      ((ω ^ (-(c.val : ℤ))) g : k) • e₁ (x.2 c)
    rw [← hy, he₁, modRep_mk, map_smul, he₁]
    funext j
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • algebraMap O k (((Γ.chi (c.val + 1) g : Oˣ) : O) * y) =
      ((ω ^ (-(c.val : ℤ))) g : k) * algebraMap O k y
    rw [Algebra.smul_def, ← map_mul, ← mul_assoc, ← Units.val_mul, map_mul, hω']
    congr 1
    simp [GalData.chi]

end Lat

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O}

theorem crysWith_zero {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Subsingleton V] (ρ : Representation LL G V) : CrysWith PD emb ρ (fun _ => 0) := by
  refine ⟨?_, fun i τ _ a => ?_⟩
  · rw [IsCrys, Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := V), mul_zero]
  · rw [multV, Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
    simp

theorem crysWith_pi [IsTopologicalRing LL] (hsum : StdAdm.SumRule PD emb O) {U : ZMod n → Multiset ℤ} :
    ∀ (μ : ℕ) (T : LocLat G Qp LL O) (F : Fin μ → LocLat G Qp LL O) (e : T.V ≃ₗ[LL] (∀ j, (F j).V)),
      (∀ g x j, e (T.ρ g x) j = (F j).ρ g (e x j)) → (∀ j, CrysWith PD emb (F j).ρ U) →
      CrysWith PD emb T.ρ (fun i => μ • U i)
  | 0, T, F, e, _, _ => by
    have : Subsingleton T.V := e.toEquiv.subsingleton
    simpa using crysWith_zero T.ρ
  | μ + 1, T, F, e, he, hF => by
    have ih := crysWith_pi hsum μ (piLoc fun j => F j.succ) (fun j => F j.succ) (LinearEquiv.refl _ _)
      (fun _ _ _ => rfl) fun j => hF _
    have h := hsum (F 0) (piLoc fun j => F j.succ) T _ _
      (e.trans (Fin.consLinearEquiv LL fun j => (F j).V).symm)
      (fun g x => Prod.ext (he g x 0) (funext fun j => he g x j.succ)) (hF 0) ih
    simpa only [succ_nsmul'] using h

theorem sumFull_crys [IsTopologicalRing LL] (hsum : StdAdm.SumRule PD emb O) {t μ : ℕ} {U : ZMod n → Multiset ℤ}
    {T : LocLat G Qp LL O} (h : SumFull PD emb Γ t U μ T) : CrysWith PD emb T.ρ (fun i => μ • U i) := by
  obtain ⟨F, hF, e, he⟩ := h
  exact crysWith_pi hsum μ T F e he fun j => (hF j).1

theorem sumFull_sameSS [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    {t μ : ℕ} {U : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (h : SumFull PD emb Γ t U μ T) :
    SameSS (modRep (latRep T.L) Γ.lam) (piRep fun _ : Fin μ => Γ.refRep t) := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨L, u, hu⟩ := piLattice T F e he
  let p : ↥L.T →ₗ[O] (∀ j, QuotSMulTop Γ.lam ↥(F j).L.T) :=
    (LinearMap.pi fun j => (Submodule.mkQ _).comp (LinearMap.proj j)).comp u.toLinearMap
  have hp : ∀ x j, p x j = Submodule.Quotient.mk (u x j) := fun _ _ => rfl
  obtain ⟨f, hf⟩ := StdAdm.exists_modRep_equiv (latRep L) (piRep fun j => modRep (latRep (F j).L) Γ.lam) Γ.lam p
    (fun y => by
      choose x hx using fun j => Submodule.Quotient.mk_surjective _ (y j)
      exact ⟨u.symm x, funext fun j => by rw [hp, LinearEquiv.apply_symm_apply, hx]⟩)
    (fun x => by
      simp only [funext_iff, hp, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
      constructor
      · intro h
        choose b hb using h
        refine ⟨u.symm b, u.injective ?_⟩
        rw [map_smul, LinearEquiv.apply_symm_apply]
        exact funext hb
      · rintro ⟨y, rfl⟩ j
        rw [map_smul]
        exact ⟨_, rfl⟩)
    (fun g x => funext fun j => by
      rw [hp, piRep_apply, hp, modRep_mk]
      congr 1
      apply Subtype.ext
      rw [hu, latRep_apply, latRep_apply, hu, he])
  exact ((reduction_sameSS_of_lattices T.ρ T.L L Γ.lam hlam).congr_right f hf).trans
    (SameSS.piRep fun j => (hF j).2 (F j).L)

theorem exists_sum_ind [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hsum : StdAdm.SumRule PD emb O) {U : ZMod n → Multiset ℤ} {w : ZMod n → ℤ} (h0 : CrysWith PD emb Γ.T₀.ρ U)
    (hχ : ∀ c : ℕ, IsCrysChar PD emb (Γ.chi (c + 1)) (fun i => w i + c)) (Q : ℕ → LocLat G Qp LL O → Prop)
    (hQ0 : Q 0 Γ.T₀) (hQ : ∀ (k : ℕ) T, CrysWith PD emb T.ρ (fun i => U i + block (w i) k) → Q k T →
      Q (k + 1) (AdmClosure.prodLoc T (charLat Qp hinj _ (hχ k).1))) (k : ℕ) :
    ∃ (T : LocLat G Qp LL O) (e : ↥T.L.T ≃ₗ[O] (↥Γ.T₀.L.T × (Fin k → O))),
      CrysWith PD emb T.ρ (fun i => U i + block (w i) k) ∧ Q k T ∧
      ∀ g x, e (latRep T.L g x) = (Γ.W₀ g (e x).1, fun c : Fin k => Γ.Wchi (c.val + 1) g ((e x).2 c)) := by
  induction k with
  | zero =>
    refine ⟨Γ.T₀, (LinearEquiv.prodUnique).symm, ?_, hQ0, fun g x => Prod.ext rfl (Subsingleton.elim _ _)⟩
    simpa [block] using h0
  | succ k ih =>
    obtain ⟨T, e, hT, hq, he⟩ := ih
    obtain ⟨e₁, -, he₁⟩ := charLattice_equiv hinj (Γ.chi (k + 1))
    let C : LocLat G Qp LL O := charLat Qp hinj _ (hχ k).1
    let e₁' : O ≃ₗ[O] ↥C.L.T := e₁
    have he₁' : ∀ g y, e₁'.symm (latRep C.L g y) = Γ.Wchi (k + 1) g (e₁'.symm y) := by
      intro g y
      obtain ⟨a, rfl⟩ := e₁'.surjective y
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_apply]
      exact (he₁ g a).symm
    let s : ((↥Γ.T₀.L.T × (Fin k → O)) × O) ≃ₗ[O] (↥Γ.T₀.L.T × (Fin (k + 1) → O)) :=
      { toFun := fun x => (x.1.1, Fin.snoc (α := fun _ => O) x.1.2 x.2)
        invFun := fun y => ((y.1, Fin.init y.2), y.2 (Fin.last k))
        map_add' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        map_smul' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    let v : ↥(AdmClosure.prodLoc T C).L.T ≃ₗ[O] (↥T.L.T × ↥C.L.T) := StdAdm.prodSubEquiv T.L.T C.L.T
    refine ⟨AdmClosure.prodLoc T C, v.trans ((e.prodCongr e₁'.symm).trans s), ?_, hQ k T hT hq, fun g x => ?_⟩
    · have h := hsum T C (AdmClosure.prodLoc T C) _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) hT (hχ k).2
      simpa only [StdAdm.block_succ, add_assoc] using h
    · change s (e (latRep T.L g (v x).1), e₁'.symm (latRep C.L g (v x).2)) =
        (Γ.W₀ g (e (v x).1).1, fun c : Fin (k + 1) => Γ.Wchi (c.val + 1) g
          (Fin.snoc (α := fun _ => O) (e (v x).1).2 (e₁'.symm (v x).2) c))
      rw [he, he₁']
      refine Prod.ext rfl ?_
      funext c
      change Fin.snoc (α := fun _ => O) _ _ c = _
      refine Fin.lastCases ?_ (fun c => ?_) c
      · simp only [Fin.snoc_last, Fin.val_last]
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]

end Per

theorem omega_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (k : Type) [Field k]
    [Algebra S.O k] [CharP k l] (ω : S.G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap S.O k (S.Γ.ε g))
    (e : ℕ) (h0 : 0 < e) (h1 : e + 1 < l) : ω ^ e ≠ 1 := by
  obtain ⟨χ, hχ, -, hs⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hz
  let a : ℕ := (z : ZMod l).val
  have ha : (a : ZMod l) = z := ZMod.natCast_zmod_val _
  have hu : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime z).symm
  have hK : S.K.1 ≤ Ks S.K 0 := le_trans (le_inf le_rfl S.hyp.1.2.1.1) le_sup_left
  obtain ⟨g, hg, hgu⟩ := hs S.K 0 hK hu.unit (by simp)
  have h2 : (S.Γ.ε ⟨g, hg⟩ : S.O) = a := by
    apply Subtype.ext
    have h3 := S.hyp.2.1.2.2.2 ⟨g, hg⟩
    rw [P.PD_χ, ← hχ, hgu] at h3
    simpa using h3
  intro h
  have h4 : ((ω ⟨g, hg⟩ : kˣ) : k) ^ e = 1 := by
    have := congrArg (fun f : S.G →* kˣ => ((f ⟨g, hg⟩ : kˣ) : k)) h
    simpa using this
  rw [hω, h2, map_natCast] at h4
  have h5 : (z : ZMod l) ^ e = 1 := by
    apply (ZMod.castHom (dvd_refl l) k).injective
    rw [← ha, map_pow, map_natCast, h4, map_one]
  have h6 : z ^ e = 1 := Units.ext (by simpa using h5)
  have := Nat.le_of_dvd h0 (orderOf_dvd_of_pow_eq_one h6)
  omega

end GlobalTheory.BasePairs
