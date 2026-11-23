import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldAscent

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hle : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U))
    (y : Y) (hy : y ∈ V) : gs (𝟙 Y) y V ((f.appLE U V hle).hom a) = gs f y U a := by
  have e : (f.appLE U V hle).hom a = (Y.presheaf.map (homOfLE hle).op).hom ((f.app U).hom a) := rfl
  rw [e, gs_res (𝟙 Y) y hle hy, gs_pull (𝟙 Y) f y U (hle hy), Category.id_comp]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {I : Type} (s : Finset I)
    (a : I → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem gs_algX {Y : Scheme.{0}} {A : Type} [CommRing A] (q : Y ⟶ Spec (CommRingCat.of A)) (W : Y.Opens) (s : A)
    (y : Y) (hy : y ∈ W) :
    gs (𝟙 Y) y W (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q W s) = gs q y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom s) :=
  gs_appLE q ⊤ W _ _ y hy

theorem local_ascent (k K : Type) [Field k] [Field K] (ι : k →+* K) (X X' : Scheme.{0}) (p : X ⟶ Sp k)
    (p' : X' ⟶ Sp K) (φ : X' ⟶ X) (H : IsPullback φ p' p (spMap ι)) (U : X.Opens) (n : ℕ) (B : Fin n → Γ(X, U))
    (d : Fin n → K)
    (hv : ∀ (z : X') (_ : φ z ∈ U),
      ∑ i, gs p' z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (d i)) * gs φ z U (B i) = 0)
    (lam : K →+ k) (hlam : ∀ c y, lam (ι c * y) = c * lam y) (x : X) (hx : x ∈ U) :
    ∑ i, gs p x ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (lam (d i))) * gs (𝟙 X) x U (B i) = 0 := by
  letI := ι.toAlgebra
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
  letI : Algebra k Γ(X, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  let lam' : K →ₗ[k] k :=
    { toFun := lam, map_add' := lam.map_add
      map_smul' := fun c y => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.id_apply, smul_eq_mul]
        exact hlam c y }
  let t : Γ(X, V) ⊗[k] K := ∑ i, ReciprocityTheory.ChartRestriction.G.DVR.rs hVU (B i) ⊗ₜ[k] d i
  have ht : t = 0 := by
    apply (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p p' φ H V hV).injective
    rw [map_zero]
    apply fn_ext
    intro z hz
    have hzV : φ z ∈ V := hz.1
    simp only [t, map_sum, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul]
    rw [gs_zero', gs_sum' _ _ _ hz, ← hv z (hVU hzV)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have et := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul p p' φ H V hV (ReciprocityTheory.ChartRestriction.G.DVR.rs hVU (B i)) (d i)
    erw [et]
    rw [gs_mul (𝟙 X') z _ hz, gs_appLE φ V _ _ _ z hz, gs_algX _ _ _ _ hz, gs_res φ z hVU hzV, mul_comm]
  have e := congrArg (fun q => TensorProduct.rid k Γ(X, V) (LinearMap.lTensor Γ(X, V) lam' q)) ht
  simp only [t, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at e
  have e2 := congrArg (gs (𝟙 X) x V) e
  rw [gs_sum' _ _ _ hxV, gs_zero'] at e2
  rw [← e2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, gs_mul (𝟙 X) x _ hxV, RingHom.algebraMap_toAlgebra, gs_algX p V _ x hxV, gs_res (𝟙 X) x hVU hxV]
  rfl

end GlobalTheory.FieldAscent

namespace GlobalTheory.FieldAscent

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun i j => by simp⟩

theorem indepAlong_ascent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (𝟙 (Sp R))))) (k K : Type) [Field k] [Field K] (ψ : R →+* k)
    (ι : k →+* K), L.IsLB → IndepAlong G L N (toBase ψ) b → IndepAlong G L N (toBase (ι.comp ψ)) b := by
  intro R _ G L N n b k K _ _ ψ ι hL hind c c' s hc hc'
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  let T₁ : Over (Sp R) := Over.mk (spMap ψ)
  let T₂ : Over (Sp R) := Over.mk (spMap (ι.comp ψ))
  have hsp : spMap ι ≫ spMap ψ = spMap (ι.comp ψ) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let h' : T₂ ⟶ T₁ := Over.homMk (spMap ι) hsp
  have hw : (toBase (ι.comp ψ) ▷ G).left = (h' ▷ G).left ≫ (toBase ψ ▷ G).left := by
    have : h' ≫ toBase ψ = toBase (ι.comp ψ) := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hsp)
    rw [← this, MonoidalCategory.comp_whiskerRight, Over.comp_left]
  have pb : IsPullback (h' ▷ G).left (fst T₂ G).left (fst T₁ G).left (spMap ι) := isPullback_whisker G h'
  have hvan : ∀ (z : (T₂ ⊗ G).left) (J), Good L z J →
      ∑ i, gs (fst T₂ G).left z ⊤ (c i - c' i) *
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i)
          (toBase (ι.comp ψ) ▷ G).left z J = 0 := by
    intro z J hJ
    have e := (hc z J hJ).symm.trans (hc' z J hJ)
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_sub, map_sub, sub_mul]
  letI := ι.toAlgebra
  let d : Fin n → K := fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (c i - c' i)
  have hd : ∀ i, d i = 0 := by
    intro i
    refine (Module.forall_dual_apply_eq_zero_iff k (d i)).1 fun lam => ?_
    let a : Fin n → Γ(T₁.left, ⊤) := fun i => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (lam (d i))
    have l0 : ∀ x J, sval (L := L) (φ := fun _ : Fin 1 => (snd T₁ G).left) (ε := fun _ => (N : ℤ))
        (zeroSec (LPow G L (N : ℤ) T₁)) (𝟙 _) x J = 0 := fun x J => gs_zero' _ _ _
    have hlin : Lin G L N (toBase ψ) b a (zeroSec _) := by
      intro x J hJ
      refine (l0 x J).trans (Eq.symm ?_)
      let r₁ := (toBase ψ ▷ G).left
      let j := J (r₁ ≫ (snd T G).left)
      let U₀ := LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => j)
      have hx : r₁ x ∈ U₀ := hJ.mem _ r₁
      have key := local_ascent k K ι _ _ (fst T₁ G).left (fst T₂ G).left (h' ▷ G).left pb (r₁ ⁻¹ᵁ U₀) n
        (fun i => (r₁.app U₀).hom ((b i).f (fun _ => j))) d ?_ lam.toAddMonoidHom
        (fun c y => lam.map_smul c y) x hx
      · rw [← key]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
      · intro z hz
        have hz' : ((toBase (ι.comp ψ) ▷ G).left ≫ (snd T G).left) z ∈ L.U j := by
          rw [hw]
          exact Set.mem_iInter.1 hz 0
        obtain ⟨J', hJ', eJ⟩ := exists_good L hL z (K := Fin 1)
          (fun _ => (toBase (ι.comp ψ) ▷ G).left ≫ (snd T G).left) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hz')
        rw [← hvan z J' hJ']
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        · simp [d]
        · have e2 : (h' ▷ G).left ≫ r₁ = (toBase (ι.comp ψ) ▷ G).left := hw.symm
          refine (gs_pull (h' ▷ G).left r₁ z U₀ hz _).trans ?_
          rw [e2]
          exact (sval_of (b i) _ z J' (fun _ => j) (fun k => eJ k)).symm
    have hlin0 : Lin G L N (toBase ψ) b 0 (zeroSec _) := by
      intro x J hJ
      refine (l0 x J).trans ?_
      simp [gs_zero']
    have := congrFun (hind a 0 _ hlin hlin0) i
    simpa [a] using congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom this
  funext i
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (hd i)
  simp only [d, map_zero] at this
  exact sub_eq_zero.1 (by simpa using this)

end GlobalTheory.FieldAscent
