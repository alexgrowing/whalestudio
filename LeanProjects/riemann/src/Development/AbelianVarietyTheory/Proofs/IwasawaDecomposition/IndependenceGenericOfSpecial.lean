import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppWhiskerRightInjectiveOfFlat

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndepFibre

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by simp⟩

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {I : Type} [Fintype I]
    (a : I → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by simp only [gs_eq f y U h, map_sum]

theorem stalkMap_gs {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)) :
    (f.stalkMap z).hom (gs g (f z) U a) = gs (f ≫ g) z U a := by
  by_cases h : g (f z) ∈ U
  · rw [gs_eq g (f z) U h, gs_eq (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _).trans rfl
  · have h' : ¬ (f ≫ g) z ∈ U := by simpa using h
    simp only [gs, h, h', dif_neg, not_false_eq_true, map_zero]

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ)

theorem sval_zeroSec {T' : Over S} {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ G).left) (z : Z) (J : (Z ⟶ G.left) → L.ι) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (zeroSec (LPow G L (N : ℤ) T')) r z J
      = 0 :=
  gs_zero _ _ _

theorem indepAlong_iff {T T' : Over S} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) :
    IndepAlong G L N h b ↔ ∀ c, Lin G L N h b c (zeroSec _) → c = 0 := by
  constructor
  · intro H c hc
    refine H c 0 _ hc fun z J hJ => ?_
    rw [sval_zeroSec]
    simp [gs_zero]
  · intro H c c' s hc hc'
    have := H (c - c') fun z J hJ => by
      rw [sval_zeroSec]
      have e := (hc z J hJ).symm.trans (hc' z J hJ)
      simp only [Pi.sub_apply, gs_sub _ z ⊤ trivial, sub_mul, Finset.sum_sub_distrib]
      rw [e, sub_self]
    exact sub_eq_zero.1 this

theorem lin_mul {T T' : Over S} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) (u : Γ(T'.left, ⊤)) (hc : Lin G L N h b c (zeroSec _)) :
    Lin G L N h b (fun i => u * c i) (zeroSec _) := by
  intro z J hJ
  have e := hc z J hJ
  rw [sval_zeroSec] at e ⊢
  simp only [gs_mul _ z ⊤ trivial, mul_assoc, ← Finset.mul_sum, ← e, mul_zero]

theorem whisker_comp {T T' T'' : Over S} (h : T' ⟶ T) (m : T'' ⟶ T') :
    ((m ≫ h) ▷ G).left = (m ▷ G).left ≫ (h ▷ G).left := by
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left]

theorem gs_fst {T' T'' : Over S} (m : T'' ⟶ T') {Y : Scheme.{0}} (r : Y ⟶ (T'' ⊗ G).left) (y : Y) (c : Γ(T'.left, ⊤)) :
    gs (r ≫ (m ▷ G).left ≫ (fst T' G).left) y ⊤ c = gs (r ≫ (fst T'' G).left) y ⊤ (m.left.appTop.hom c) := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc]
  exact (gs_pull _ _ y ⊤ trivial _).symm

theorem lin_pull {T T' T'' : Over S} (h : T' ⟶ T) (m : T'' ⟶ T') {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) (hc : Lin G L N h b c (zeroSec _)) :
    Lin G L N (m ≫ h) b (fun i => m.left.appTop.hom (c i)) (zeroSec _) := by
  intro z J hJ
  have hJ' : Good L ((m ▷ G).left z) (fun ψ => J ((m ▷ G).left ≫ ψ)) := fun ψ => hJ ((m ▷ G).left ≫ ψ)
  have e := congrArg ((m ▷ G).left.stalkMap z).hom (hc _ _ hJ')
  rw [sval_zeroSec, map_zero, map_sum] at e
  rw [sval_zeroSec]
  refine e.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul]
  congr 1
  · rw [stalkMap_gs]
    simpa using gs_fst G m (𝟙 _) z (c i)
  · rw [sval_of (b i) (h ▷ G).left _ _ (fun _ => J ((m ▷ G).left ≫ (h ▷ G).left ≫ (snd T G).left)) (fun _ => rfl),
      sval_of (b i) ((m ≫ h) ▷ G).left z J (fun _ => J ((m ▷ G).left ≫ (h ▷ G).left ≫ (snd T G).left))
        (fun _ => by rw [whisker_comp, Category.assoc])]
    exact (stalkMap_gs _ _ z _ _).trans (by rw [whisker_comp])

theorem lin_descend [Flat G.hom] (hL : L.IsLB) {T T' T'' : Over S} [IsAffine T'.left] [IsAffine T''.left]
    (h : T' ⟶ T) (m : T'' ⟶ T') (hm : Function.Injective m.left.appTop.hom) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (hc : Lin G L N (m ≫ h) b (fun i => m.left.appTop.hom (c i)) (zeroSec _)) : Lin G L N h b c (zeroSec _) := by
  intro w J hJ
  rw [sval_zeroSec]
  let j : Fin 1 → L.ι := fun _ => J ((h ▷ G).left ≫ (snd T G).left)
  let W := LB.wchart L (fun _ : Fin 1 => (snd T G).left) j
  let W' := (h ▷ G).left ⁻¹ᵁ W
  have hle : W' ≤ (fst T' G).left ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ((T' ⊗ G).left, W') := ∑ i, ((T' ⊗ G).left.presheaf.map (homOfLE hle).op).hom
      (((fst T' G).left.app ⊤).hom (c i)) * (((h ▷ G).left.app W).hom ((b i).f j))
  have key : ∀ {Y : Scheme.{0}} (r : Y ⟶ (T' ⊗ G).left) (y : Y), r y ∈ W' →
      gs r y W' a = ∑ i, gs (r ≫ (fst T' G).left) y ⊤ (c i) * gs (r ≫ (h ▷ G).left) y W ((b i).f j) := by
    intro Y r y hy
    rw [gs_sum r y W' hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul r y W' hy, gs_res r y hle hy, gs_pull r _ y ⊤ trivial]
    exact congrArg _ (gs_pull r _ y W hy _)
  have hw : w ∈ W' := hJ.mem (fun _ : Fin 1 => (snd T G).left) (h ▷ G).left
  refine Eq.trans ?_ ((key (𝟙 _) w hw).trans (Finset.sum_congr rfl fun i _ => ?_))
  · suffices ha : a = 0 by rw [ha, gs_zero]
    apply GlobalTheory.app_whiskerRight_injective_of_flat S G T' T'' m hm W'
    rw [map_zero]
    refine fn_ext fun z hz => ?_
    rw [gs_zero, gs_pull (𝟙 _) _ z W' hz, Category.id_comp, key _ z hz]
    have hmem : (((m ≫ h) ▷ G).left ≫ (snd T G).left) z ∈ L.U (j 0) := by
      rw [whisker_comp]; exact Set.mem_iInter.1 hz 0
    obtain ⟨J'', hJ'', e⟩ := exists_good L hL z (fun _ : Unit => ((m ≫ h) ▷ G).left ≫ (snd T G).left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => hmem)
    have e2 := hc z J'' hJ''
    rw [sval_zeroSec] at e2
    refine (Finset.sum_congr rfl fun i _ => ?_).trans e2.symm
    rw [sval_of (b i) ((m ≫ h) ▷ G).left z J'' j (fun _ => e ()), whisker_comp]
    congr 1
    simpa using gs_fst G m (𝟙 _) z (c i)
  · rw [Category.id_comp, Category.id_comp]; rfl

theorem indepAlong_generic : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (𝟙 (Sp R))))) (K : Type) [Field K] (V : ValuationSubring K)
    (g : R →+* V), Flat G.hom → L.IsLB → IndepAlong G L N (toBase ((IsLocalRing.residue V).comp g)) b →
    IndepAlong G L N (toBase (V.subtype.comp g)) b := by
  intro R _ G L N n b K _ V g hG hL hI
  rw [indepAlong_iff] at hI ⊢
  intro c hc
  by_contra hne
  let e : Fin n → K := fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (c i)
  have hce : ∀ i, c i = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (e i) := fun i => by simp [e]
  obtain ⟨i₁, hi₁⟩ : ∃ i, e i ≠ 0 := by
    by_contra H
    push_neg at H
    exact hne (funext fun i => by rw [hce i, H i, map_zero]; rfl)
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (e i)) ⟨i₁, Finset.mem_univ _⟩
  have hi₀ : e i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  have hd : ∀ i, e i / e i₀ ∈ V := fun i => by
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax i (Finset.mem_univ _)) zero_le'
  let d : Fin n → V := fun i => ⟨e i / e i₀, hd i⟩
  have hd₀ : d i₀ = 1 := Subtype.ext (div_self hi₀)
  let cV : Fin n → Γ(Sp V, ⊤) := fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (d i)
  haveI := hG
  haveI : IsAffine (Over.mk (spMap g)).left := inferInstanceAs (IsAffine (Sp V))
  haveI : IsAffine (Over.mk (spMap (V.subtype.comp g))).left := inferInstanceAs (IsAffine (Sp K))
  let mK : Over.mk (spMap (V.subtype.comp g)) ⟶ Over.mk (spMap g) :=
    Over.homMk (spMap V.subtype) (by simp only [Over.mk_hom, spMap, ← Spec.map_comp]; rfl)
  let mk : Over.mk (spMap ((residue V).comp g)) ⟶ Over.mk (spMap g) :=
    Over.homMk (spMap (residue V)) (by simp only [Over.mk_hom, spMap, ← Spec.map_comp]; rfl)
  have hK : mK ≫ toBase g = toBase (V.subtype.comp g) := Over.OverMorphism.ext (Over.w mK)
  have hk : mk ≫ toBase g = toBase ((residue V).comp g) := Over.OverMorphism.ext (Over.w mk)
  have appK : ∀ x : V, mK.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x : K) := fun x => by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom V.subtype)
    exact (congrArg (fun φ => φ.hom x) this).symm
  have appk : ∀ x : V, mk.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V))).inv.hom (residue V x) := fun x => by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue V))
    exact (congrArg (fun φ => φ.hom x) this).symm
  have inj : Function.Injective mK.left.appTop.hom := by
    intro x y hxy
    have ex : ∀ z : Γ(Sp V, ⊤), z = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom z) := fun z => by simp
    rw [ex x, ex y, appK, appK] at hxy
    have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom hxy
    simp only [Iso.inv_hom_id_apply, CommRingCat.hom_inv_apply] at h'
    rw [ex x, ex y, Subtype.ext h']
  let u : Γ((Over.mk (spMap (V.subtype.comp g))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (e i₀)⁻¹
  have h1 := lin_mul G L N _ b c u hc
  have h2 : (fun i => u * c i) =
      fun i => mK.left.appTop.hom (cV i) := by
    funext i
    rw [appK, hce i, ← map_mul]
    simp only [d, div_eq_inv_mul]
  rw [h2, ← hK] at h1
  have h3 := lin_descend G L N hL (toBase g) mK inj b cV h1
  have h4 := lin_pull G L N (toBase g) mk b cV h3
  rw [hk] at h4
  have h5 := congrFun (hI _ h4) i₀
  rw [Pi.zero_apply, appk, hd₀, map_one, map_one] at h5
  have h6 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V))).hom.hom h5
  simp at h6

end GlobalTheory.IndepFibre
