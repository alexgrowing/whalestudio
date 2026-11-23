import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BalancedLiftTmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w w'

namespace GlobalTheory.CompanionTheory.CosieveBC

open CrystallineSemistableComparison.CechClassBoundaries

section Cxs

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {ι : Type} {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

def Lin {K : ι → Cx.{w} R} {K' : Cx.{w'} R'} (φ : ∀ i, N i → Cx.Hom (K i) K' σ) : Prop :=
  (∀ i n n' k x, (φ i (n + n')).f k x = (φ i n).f k x + (φ i n').f k x) ∧
    ∀ i (r : R) n k x, (φ i (r • n)).f k x = σ r • (φ i n).f k x

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem bal_mapH {K : ι → Cx.{w} R} {K' : Cx.{w'} R'} {φ : ∀ i, N i → Cx.Hom (K i) K' σ} (h : Lin φ) (j : ℕ) :
    Bal R (N := N) (M := fun i => (K i).H j) (P := K'.H j) fun i n x => (φ i n).mapH j x := by
  refine ⟨fun i n n' x => ?_, fun i n x x' => map_add _ _ _, fun i r n x => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := clsSurj x
    have c1 := cyc (φ i n) a ha
    have c2 := cyc (φ i n') a ha
    beta_reduce
    rw [mapH_cls' _ a ha (cyc _ a ha), mapH_cls' _ a ha c1, mapH_cls' _ a ha c2,
      ← cls_add _ _ c1 c2 (by rw [map_add, c1, c2, add_zero])]
    exact cls_congr (h.1 i n n' j a) _ _
  · obtain ⟨a, ha, rfl⟩ := clsSurj x
    have c1 := cyc (φ i n) a ha
    beta_reduce
    rw [map_smulₛₗ, mapH_cls' _ a ha (cyc _ a ha), mapH_cls' _ a ha c1,
      ← cls_smul _ _ c1 (by rw [map_smul, c1, smul_zero])]
    exact cls_congr (h.2 i r n j a) _ _

theorem sq_mapH {A : Cx.{w} R} {B : Cx.{w} R} {A' : Cx.{w'} R'} {B' : Cx.{w'} R'} (f : Cx.Hom A B (RingHom.id R))
    (f' : Cx.Hom A' B' (RingHom.id R')) (φ : Cx.Hom A A' σ) (ψ : Cx.Hom B B' σ)
    (c : ∀ k x, ψ.f k (f.f k x) = f'.f k (φ.f k x)) (k : ℕ) (z : A.H k) :
    f'.mapH k (φ.mapH k z) = ψ.mapH k (f.mapH k z) := by
  obtain ⟨a, ha, rfl⟩ := clsSurj z
  have c1 := cyc φ a ha
  have c2 := cyc f a ha
  rw [mapH_cls' φ a ha c1, mapH_cls' f' _ c1 (cyc f' _ c1), mapH_cls' f a ha c2, mapH_cls' ψ _ c2 (cyc ψ _ c2)]
  exact cls_congr (c k a).symm _ _

theorem les_pair {A B D : ι → Cx.{w} R} {A' B' D' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (A i) (B i) (RingHom.id R)) (g : ∀ i, Cx.Hom (B i) (D i) (RingHom.id R))
    (f' : Cx.Hom A' B' (RingHom.id R')) (g' : Cx.Hom B' D' (RingHom.id R'))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (φA : ∀ i, N i → Cx.Hom (A i) A' σ) (φB : ∀ i, N i → Cx.Hom (B i) B' σ) (φD : ∀ i, N i → Cx.Hom (D i) D' σ)
    (c1 : ∀ i m k x, (φB i m).f k ((f i).f k x) = f'.f k ((φA i m).f k x))
    (c2 : ∀ i m k x, (φD i m).f k ((g i).f k x) = g'.f k ((φB i m).f k x)) :
    ∃ (δ : ∀ i k, (D i).H k →ₗ[R] (A i).H (k + 1)) (δ' : ∀ k, D'.H k →ₗ[R'] A'.H (k + 1)),
      (∀ i, Function.Injective ((f i).mapH 0)) ∧ (∀ i k, Function.Exact ((f i).mapH k) ((g i).mapH k)) ∧
      (∀ i k, Function.Exact ((g i).mapH k) (δ i k)) ∧ (∀ i k, Function.Exact (δ i k) ((f i).mapH (k + 1))) ∧
      Function.Injective (f'.mapH 0) ∧ (∀ k, Function.Exact (f'.mapH k) (g'.mapH k)) ∧
      (∀ k, Function.Exact (g'.mapH k) (δ' k)) ∧ (∀ k, Function.Exact (δ' k) (f'.mapH (k + 1))) ∧
      ∀ i m k z, δ' k ((φD i m).mapH k z) = (φA i m).mapH (k + 1) (δ i k z) := by
  have L := fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  choose δ hδ i0 e1 e2 e3 using L
  obtain ⟨δ', hδ', i0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  refine ⟨δ, δ', i0, e1, e2, e3, i0', e1', e2', e3', fun i m k z => ?_⟩
  obtain ⟨d, hd, rfl⟩ := clsSurj z
  obtain ⟨y, rfl⟩ := hg i k d
  obtain ⟨x, hx⟩ := conn_ex (f i) (g i) (hfg i) y hd
  have hxc := conn_cyc (f i) (hf i) y x hx
  rw [hδ i k y x hd hxc hx, mapH_cls' (φA i m) _ hxc (cyc _ _ hxc)]
  have h2 : D'.d k (g'.f k ((φB i m).f k y)) = 0 := by
    rw [← c2]
    exact cyc _ _ hd
  have e : (φD i m).mapH k ((D i).cls ((g i).f k y) hd) = D'.cls (g'.f k ((φB i m).f k y)) h2 := by
    rw [mapH_cls' _ _ hd (cyc _ _ hd)]
    exact cls_congr (c2 i m k y) _ _
  rw [e]
  refine hδ' k _ _ h2 _ ?_
  rw [← c1, hx, (φB i m).comm]

theorem subsingleton_tensor {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Subsingleton Q] :
    Subsingleton (P ⊗[R] Q) := by
  refine subsingleton_of_forall_eq 0 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
  | add s t hs ht => rw [hs, ht, add_zero]

theorem tens_subsingleton [DecidableEq ι] {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {P : Type w'} [AddCommGroup P] [∀ i, Subsingleton (M i)] [Subsingleton P] (p : ∀ i, N i → M i → P) :
    Tens R (N := N) (M := M) (M' := P) p := by
  have : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => subsingleton_tensor
  exact ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _⟩, fun _ _ _ => Subsingleton.elim _ _⟩

theorem bal_unit :
    Bal R (N := N) (M := fun _ : ι => PUnit.{w + 1}) (P := PUnit.{w' + 1}) fun _ _ _ => PUnit.unit :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def BC [DecidableEq ι] {K : ι → Cx.{w} R} {K' : Cx.{w'} R'} (φ : ∀ i, N i → Cx.Hom (K i) K' σ) : Prop :=
  ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (φ i n).mapH j x

theorem exact_of_inj {X Y Z : Type*} [Nonempty X] [Zero Y] [Zero Z] (a : X → Y) (f : Y → Z) (ha : ∀ x, a x = 0)
    (hf0 : f 0 = 0) (h : Function.Injective f) : Function.Exact a f := by
  intro y
  constructor
  · intro hy
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨x, by rw [ha, h (hy.trans hf0.symm)]⟩
  · rintro ⟨x, rfl⟩
    rw [ha, hf0]

theorem bc_ses [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {A B D : ι → Cx.{w} R} {A' B' D' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (A i) (B i) (RingHom.id R)) (g : ∀ i, Cx.Hom (B i) (D i) (RingHom.id R))
    (f' : Cx.Hom A' B' (RingHom.id R')) (g' : Cx.Hom B' D' (RingHom.id R'))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (φA : ∀ i, N i → Cx.Hom (A i) A' σ) (φB : ∀ i, N i → Cx.Hom (B i) B' σ) (φD : ∀ i, N i → Cx.Hom (D i) D' σ)
    (lA : Lin φA) (lB : Lin φB) (lD : Lin φD)
    (c1 : ∀ i m k x, (φB i m).f k ((f i).f k x) = f'.f k ((φA i m).f k x))
    (c2 : ∀ i m k x, (φD i m).f k ((g i).f k x) = g'.f k ((φB i m).f k x)) :
    (BC φB → BC φD → BC φA) ∧ (BC φA → BC φD → BC φB) := by
  obtain ⟨δ, δ', i0, e1, e2, e3, i0', e1', e2', e3', hδ⟩ :=
    les_pair f g f' g' hf hfg hg hf' hfg' hg' φA φB φD c1 c2
  have s1 := fun i m k z => sq_mapH (f i) f' (φA i m) (φB i m) (c1 i m) k z
  have s2 := fun i m k z => sq_mapH (g i) g' (φB i m) (φD i m) (c2 i m) k z
  refine ⟨fun tB tD j => ?_, fun tA tD j => ?_⟩
  · cases j with
    | zero =>
      exact tens_five (M₁ := fun _ => PUnit) (M₂ := fun _ => PUnit) (P₁ := PUnit) (P₂ := PUnit)
        (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
        0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
        (fun i y => ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩)
        (fun i => exact_of_inj _ _ (fun _ => rfl) (map_zero _) (i0 i)) (fun i => e1 i 0)
        (fun y => ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩)
        (exact_of_inj _ _ (fun _ => rfl) (map_zero (f'.mapH 0)) i0') (e1' 0)
        bal_unit bal_unit (bal_mapH lA 0) (bal_mapH lB 0) (bal_mapH lD 0)
        (fun _ _ _ => rfl) (fun i n x => (map_zero ((φA i n).mapH 0)).symm)
        (fun i n x => s1 i n 0 x) (fun i n x => s2 i n 0 x)
        (tens_subsingleton _) (tens_subsingleton _) (tB 0) (tD 0)
    | succ j =>
      exact tens_five (fun i => (g i).mapH j) (fun i => δ i j) (fun i => (f i).mapH (j + 1)) (fun i => (g i).mapH (j + 1))
        (g'.mapH j).toAddMonoidHom (δ' j).toAddMonoidHom (f'.mapH (j + 1)).toAddMonoidHom (g'.mapH (j + 1)).toAddMonoidHom
        (fun i => e2 i j) (fun i => e3 i j) (fun i => e1 i (j + 1)) (e2' j) (e3' j) (e1' (j + 1))
        (bal_mapH lB j) (bal_mapH lD j) (bal_mapH lA (j + 1)) (bal_mapH lB (j + 1)) (bal_mapH lD (j + 1))
        (fun i n x => s2 i n j x) (fun i n x => hδ i n j x) (fun i n x => s1 i n (j + 1) x) (fun i n x => s2 i n (j + 1) x)
        (tB j) (tD j) (tB (j + 1)) (tD (j + 1))
  · cases j with
    | zero =>
      exact tens_five (M₁ := fun _ => PUnit) (P₁ := PUnit)
        (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0) (fun i => δ i 0)
        0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom (δ' 0).toAddMonoidHom
        (fun i => exact_of_inj _ _ (fun _ => rfl) (map_zero _) (i0 i)) (fun i => e1 i 0) (fun i => e2 i 0)
        (exact_of_inj _ _ (fun _ => rfl) (map_zero (f'.mapH 0)) i0') (e1' 0) (e2' 0)
        bal_unit (bal_mapH lA 0) (bal_mapH lB 0) (bal_mapH lD 0) (bal_mapH lA 1)
        (fun i n x => (map_zero ((φA i n).mapH 0)).symm) (fun i n x => s1 i n 0 x) (fun i n x => s2 i n 0 x)
        (fun i n x => hδ i n 0 x)
        (tens_subsingleton _) (tA 0) (tD 0) (tA 1)
    | succ j =>
      exact tens_five (fun i => δ i j) (fun i => (f i).mapH (j + 1)) (fun i => (g i).mapH (j + 1)) (fun i => δ i (j + 1))
        (δ' j).toAddMonoidHom (f'.mapH (j + 1)).toAddMonoidHom (g'.mapH (j + 1)).toAddMonoidHom (δ' (j + 1)).toAddMonoidHom
        (fun i => e3 i j) (fun i => e1 i (j + 1)) (fun i => e2 i (j + 1)) (e3' j) (e1' (j + 1)) (e2' (j + 1))
        (bal_mapH lD j) (bal_mapH lA (j + 1)) (bal_mapH lB (j + 1)) (bal_mapH lD (j + 1)) (bal_mapH lA (j + 2))
        (fun i n x => hδ i n j x) (fun i n x => s1 i n (j + 1) x) (fun i n x => s2 i n (j + 1) x)
        (fun i n x => hδ i n (j + 1) x)
        (tD j) (tA (j + 1)) (tD (j + 1)) (tA (j + 2))

def prodCx (K L : Cx.{w} R) : Cx.{w} R where
  X n := K.X n × L.X n
  d n := (K.d n).prodMap (L.d n)
  dd n x := Prod.ext (K.dd n x.1) (L.dd n x.2)

def prodHom {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K K' σ) (ψ : Cx.Hom L L' σ) :
    Cx.Hom (prodCx K L) (prodCx K' L') σ where
  f n :=
    { toFun := fun x => (φ.f n x.1, ψ.f n x.2)
      map_add' := fun x y => Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' := fun r x => Prod.ext (map_smulₛₗ _ _ _) (map_smulₛₗ _ _ _) }
  comm n x := Prod.ext (φ.comm n x.1) (ψ.comm n x.2)

def inlHom (K L : Cx.{w} R) : Cx.Hom K (prodCx K L) (RingHom.id R) where
  f n := LinearMap.inl R (K.X n) (L.X n)
  comm n x := Prod.ext rfl (map_zero (L.d n))

def sndHom (K L : Cx.{w} R) : Cx.Hom (prodCx K L) L (RingHom.id R) where
  f n := LinearMap.snd R (K.X n) (L.X n)
  comm n x := rfl

theorem bc_prod [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {K L : ι → Cx.{w} R} {K' L' : Cx.{w'} R'}
    (φ : ∀ i, N i → Cx.Hom (K i) K' σ) (ψ : ∀ i, N i → Cx.Hom (L i) L' σ) (hφ : Lin φ) (hψ : Lin ψ)
    (tφ : BC φ) (tψ : BC ψ) : BC fun i n => prodHom (φ i n) (ψ i n) := by
  have lP : Lin fun i n => prodHom (φ i n) (ψ i n) :=
    ⟨fun i n n' k x => Prod.ext (hφ.1 i n n' k x.1) (hψ.1 i n n' k x.2),
      fun i r n k x => Prod.ext (hφ.2 i r n k x.1) (hψ.2 i r n k x.2)⟩
  refine (bc_ses (fun i => inlHom (K i) (L i)) (fun i => sndHom (K i) (L i)) (inlHom K' L') (sndHom K' L')
    ?_ ?_ ?_ ?_ ?_ ?_ φ (fun i n => prodHom (φ i n) (ψ i n)) ψ hφ lP hψ ?_ ?_).2 tφ tψ
  · exact fun i n => LinearMap.inl_injective
  · exact fun i n y => ⟨fun hy => ⟨y.1, Prod.ext rfl hy.symm⟩, by rintro ⟨x, rfl⟩; rfl⟩
  · exact fun i n => LinearMap.snd_surjective
  · exact fun n => LinearMap.inl_injective
  · exact fun n y => ⟨fun hy => ⟨y.1, Prod.ext rfl hy.symm⟩, by rintro ⟨x, rfl⟩; rfl⟩
  · exact fun n => LinearMap.snd_surjective
  · exact fun i m k x => Prod.ext rfl (map_zero _)
  · exact fun i m k x => rfl

end Cxs

end GlobalTheory.CompanionTheory.CosieveBC
