import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PfFrom
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TestOfPre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe v' u'

namespace CrystallineSemistableComparison.D

section Abs

variable {R : Type} [CommRing R] {p : ℕ}

theorem pf_ext {X Y : PfC p R} {f g : X ⟶ Y} (h : ∀ x, f.hom.hom x = g.hom.hom x) : f = g :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext h))

theorem injUpTo_span {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Set R)
    (f : M →ₗ[R] N) (h : ∀ s ∈ S, InjUpTo s f) : ∀ s ∈ Ideal.span S, InjUpTo s f := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact zero_smul R z
  | add x y _ _ hx hy => intro z hz; rw [add_smul, hx z hz, hy z hz, add_zero]
  | smul a x _ hx => intro z hz; rw [smul_eq_mul, mul_smul, hx z hz, smul_zero]

theorem exactUpTo_span {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
    [Module R P] (S : Set R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : ∀ s ∈ S, ExactUpTo s f g) :
    ∀ s ∈ Ideal.span S, ExactUpTo s f g := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add x y _ _ hx hy =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    obtain ⟨v, hv⟩ := hy z hz
    exact ⟨u + v, by rw [map_add, hu, hv, add_smul]⟩
  | smul a x _ hx =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    exact ⟨a • u, by rw [map_smul, hu, smul_eq_mul, mul_smul]⟩

variable {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
variable (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
  (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra R (K n)] [∀ n, Algebra A.obj (K n)] [∀ n, IsScalarTower R A.obj (K n)]
  (hK : ∀ n, Pf p (K n)) (ι : ∀ n, Fin n → (B →ₐ[A.obj] K n)) (hι : ∀ n, IsWP (ι n))
  (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A.obj] K (n + 1)))
  (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
  (hrel : ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)),
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i))
  (h0 : Function.Bijective (algebraMap A.obj (K 0))) (h1 : Function.Bijective (ι 1 0))

def univMap (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) : pfOb (R := R) (K n) (hK n) ⟶ X :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { toRingHom := Classical.choose ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
        (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))
      commutes' := fun c => by
        have h := (Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
          (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))).1
        rw [IsScalarTower.algebraMap_apply R A.obj (K n)]
        exact (RingHom.congr_fun h _).trans (x.hom.hom.commutes c) })

theorem univMap_spec (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) :
    (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (algebraMap A.obj (K n)) = x.hom.hom.toRingHom ∧
      ∀ i, (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (ι n i : B →+* K n) = (y i).hom.hom.toRingHom :=
  Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
    (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))

def mkPowers : Powers j A where
  B := pfOb (R := R) B hB
  f := pfFrom A B hB
  K n := pfOb (R := R) (K n) (hK n)
  a n := pfFrom A (K n) (hK n)
  ι n i := pfHom ((ι n i).restrictScalars R)
  w n i := pf_ext fun c => (ι n i).commutes c
  δ n k := pfHom ((δ n k).restrictScalars R)
  aδ n k := pf_ext fun c => (δ n k).commutes c
  ιδ n k i := pf_ext fun c => AlgHom.congr_fun (hδ n k i) c
  rel n k i := pf_ext fun c => AlgHom.congr_fun (hrel n k i) c
  iso0 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R A.obj (K 0)) h0)).isIso_hom
  iso1 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective ((ι 1 0).restrictScalars R) h1)).isIso_hom
  univ n t x y hxy := by
    refine ⟨univMap A B hB K hK ι hι n (j.obj t) x y hxy, ⟨?_, fun i => ?_⟩, fun z hz => ?_⟩
    · exact pf_ext fun c => RingHom.congr_fun (univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).1 c
    · exact pf_ext fun c => RingHom.congr_fun ((univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).2 i) c
    · have hs := univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy
      exact pf_ext fun c => RingHom.congr_fun ((hι n).uniq (j.obj t).obj z.hom.hom.toRingHom
        (univMap A B hB K hK ι hι n (j.obj t) x y hxy).hom.hom.toRingHom
        (RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) hz.1).trans (RingHom.congr_fun hs.1 c).symm)
        (fun i => RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) (hz.2 i)).trans
          (RingHom.congr_fun (hs.2 i) c).symm)) c

theorem mkPowers_dK (N : Type) [AddCommGroup N] [Module R N] (n : ℕ) (w : N ⊗[R] K n) :
    (mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1).dK j (tensF p R N) n w = ((alt (δ n)).restrictScalars R).lTensor N w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul a b =>
    rw [Powers.dK, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, alt, LinearMap.sum_apply,
      LinearMap.sum_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact (map_zsmul (TensorProduct.mk R N (K (n + 1)) a) _ _).symm

end Abs

theorem powers_abs {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] (p : ℕ) [Fact p.Prime]
    {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
    (r : ℕ → R) (hr : IsRt p r) (hdiv : ∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M)
    (N : Type) [AddCommGroup N] [Module R N]
    (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
    (hC : Cov p (fun k => algebraMap R A.obj (r k)) B)
    (H1 : ∀ (t : T) (x : A ⟶ j.obj t), ∃ y : pfOb (R := R) B hB ⟶ j.obj t, pfFrom A B hB ≫ y = x)
    (H3 : ∃ (t₀ : T) (g : pfOb (R := R) B hB ⟶ j.obj t₀),
      (∀ (t : T) (y : pfOb (R := R) B hB ⟶ j.obj t), ∃! φ : t₀ ⟶ t, g ≫ j.map φ = y) ∧
      Almost (Ideal.span (Set.range r)) ((tensF p R N).map g).hom) :
    ∃ P : Powers j A, P.Good j (tensF p R N) (Ideal.span (Set.range r)) := by
  choose K iK aK ι hι using fun n => Leaf.wp_ex A.obj B n
  let _ : ∀ n, Algebra R (K n) := fun n => ((algebraMap A.obj (K n)).comp (algebraMap R A.obj)).toAlgebra
  have _ : ∀ n, IsScalarTower R A.obj (K n) := fun n => IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h0, h1, δ, hδ⟩ := Leaf.wp_cof A.obj B K ι hι
  have hrel := Leaf.wp_rel A.obj B K ι δ hι hδ
  have hK : ∀ n, Pf p (K n) := fun n => Leaf.wp_pf p A.obj B (K n) n (ι n) (hι n) A.property hB
  obtain ⟨hc1, hc2⟩ := Leaf.cech_tens p R r N A.obj B K ι δ hr hdiv A.property hB hC hι hδ
  refine ⟨mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1, H1, fun s hs => ⟨?_, fun n => ?_⟩, H3⟩
  · refine injUpTo_span _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    exact hc1 w hw k
  · refine exactUpTo_span _ _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    obtain ⟨x, hx⟩ := hc2 n w hw k
    exact ⟨x, (mkPowers_dK j A B hB K hK ι hι δ hδ hrel h0 h1 N n x).trans hx⟩

end CrystallineSemistableComparison.D
