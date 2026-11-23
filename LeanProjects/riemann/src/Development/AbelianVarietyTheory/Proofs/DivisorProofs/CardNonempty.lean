import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ]

instance : SemilatticeSup {I : Finset κ // I.Nonempty} :=
  Subtype.semilatticeSup fun _ _ hx _ => hx.mono Finset.subset_union_left

abbrev NE (κ : Type) [LinearOrder κ] : Type := ({I : Finset κ // I.Nonempty})ᵒᵈ

abbrev ne (s : Finset κ) (h : s.Nonempty) : (NE κ)ᵒᵖ := op (OrderDual.toDual ⟨s, h⟩)

abbrev sub (a : (NE κ)ᵒᵖ) : Finset κ := (OrderDual.ofDual a.unop).1

theorem sub_nonempty (a : (NE κ)ᵒᵖ) : (sub a).Nonempty := (OrderDual.ofDual a.unop).2

theorem sub_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : sub a ⊆ sub b := leOfHom f.unop

def homOf {a b : (NE κ)ᵒᵖ} (h : sub a ⊆ sub b) : a ⟶ b := (homOfLE (show b.unop ≤ a.unop from h)).op

def mn (a : (NE κ)ᵒᵖ) : κ := (sub a).min' (sub_nonempty a)

theorem mn_mem (a : (NE κ)ᵒᵖ) : mn a ∈ sub a := Finset.min'_mem _ _

theorem mn_le_of_hom {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : mn b ≤ mn a :=
  Finset.min'_le _ _ (sub_subset f (mn_mem a))

theorem card_nonempty {p : ℕ} (s : {s : Finset κ // s.card = p + 1}) : s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; omega)

theorem card_three {x y z : κ} (h₁ : x < y) (h₂ : y < z) : ({x, y, z} : Finset κ).card = 2 + 1 := by
  rw [Finset.card_insert_of_notMem (by simp [h₁.ne, (h₁.trans h₂).ne]), Finset.card_pair h₂.ne]

section Cech

variable {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

abbrev CC (p : ℕ) : Type := ∀ s : {s : Finset κ // s.card = p + 1}, F.obj (ne s.1 (card_nonempty s))

def δ (p : ℕ) : CC F p →ₗ[R] CC F (p + 1) :=
  LinearMap.pi fun t => ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
    ((mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
      (Finset.erase_subset i.1 t.1))).toLinearMap ∘ₗ LinearMap.proj (GlobalTheory.Cube.eraseIdx t i))

theorem δ_apply (p : ℕ) (x : CC F p) (t : {s : Finset κ // s.card = p + 1 + 1}) :
    δ F p x t = ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
      mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
        (Finset.erase_subset i.1 t.1)) (x (GlobalTheory.Cube.eraseIdx t i)) := by
  simp [δ, LinearMap.sum_apply]

def e0 : CC F 0 →ₗ[R] C0 F :=
  LinearMap.pi fun a => (mp F (homOf (a := ne {mn a} (Finset.singleton_nonempty _)) (b := a)
    (Finset.singleton_subset_iff.2 (mn_mem a)))).toLinearMap ∘ₗ
      LinearMap.proj (⟨{mn a}, Finset.card_singleton _⟩ : {s : Finset κ // s.card = 0 + 1})

theorem pair_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : ({mn b, mn a} : Finset κ) ⊆ sub b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mn_mem b
  · exact sub_subset f (mn_mem a)

theorem triple_subset {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    ({mn d, mn b, mn a} : Finset κ) ⊆ sub d := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact mn_mem d
  · exact sub_subset g (mn_mem b)
  · exact sub_subset g (sub_subset f (mn_mem a))

def e1 : CC F 1 →ₗ[R] C1 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun f =>
    if h : mn b < mn a then
      -((mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn b, mn a}, Finset.card_pair h.ne⟩ : {s : Finset κ // s.card = 1 + 1}))
    else 0

def e2 : CC F 2 →ₗ[R] C2 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun d => LinearMap.pi fun f =>
    LinearMap.pi fun g =>
    if h : mn d < mn b ∧ mn b < mn a then
      -((mp F (homOf (a := ne {mn d, mn b, mn a} (Finset.insert_nonempty _ _)) (b := d)
          (triple_subset f g))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ : {s : Finset κ // s.card = 2 + 1}))
    else 0

end Cech

section Scheme

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cov (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (I : NE κ) :
    X.affineOpens :=
  ⟨⨅ i ∈ (OrderDual.ofDual I).1, D i, hD _ (OrderDual.ofDual I).2⟩

theorem cov_mono (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    Monotone (cov D hD) := fun _ _ h => show (⨅ i ∈ _, D i) ≤ ⨅ i ∈ _, D i from biInf_mono fun _ hi => h hi

abbrev covF (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R :=
  (cov_mono D hD).functor.op ⋙ OAff s

def res0 (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    LinearMap.ker (d0 (OAff s)) →ₗ[R] LinearMap.ker (d0 (covF s D hD)) where
  toFun g := ⟨fun I => g.1 (op (cov D hD I.unop)), by
    funext I J f
    exact congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) _) _) ((cov_mono D hD).functor.map f.unop).op⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem triv_pull_U {X' : Scheme.{0}} (φ : X' ⟶ X) (j : ((LB.triv X).pull φ).ι) :
    ((LB.triv X).pull φ).U j = ⊤ := by
  ext x; simp [LB.pull, LB.LinComb, LB.wchart]

def i0 {X' : Scheme.{0}} (φ : X' ⟶ X) : ((LB.triv X).pull φ).ι := fun _ => PUnit.unit

def trivCoord {X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (V : X'.Opens) :
    GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V →ₗ[R'] Sec s' V where
  toFun x := Sec.res s' (le_inf le_rfl (by rw [triv_pull_U]; exact le_top)) (GlobalTheory.AbLaw.SecOnR.coord x (i0 φ))
  map_add' x y := by simp [GlobalTheory.AbLaw.SecOnR.coord_add]; exact map_add _ _ _
  map_smul' r x := by
    have e : (show Sec s' _ from (r • x).coord (i0 φ)) = r • (show Sec s' _ from x.coord (i0 φ)) := by
      rw [GlobalTheory.AbLaw.SecOnR.coord_base_smul]; rfl
    exact (congrArg (Sec.res s' _) e).trans (map_smul _ _ _)

def Φ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (D : κ → X.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) :
    R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p →ₗ[R'] CC (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p :=
  (LinearMap.pi fun t => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) ∘ₗ LinearMap.proj t) ∘ₗ
    GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1)

def one (s : X ⟶ Sp R) (D : κ → X.Opens) : (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X 0 :=
  fun t => GlobalTheory.AbLaw.SecOnR.of s _ _ ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1)

def pr {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (I : NE κ) : Pair ψ :=
  ⟨(cov D'' hD'' I, cov D' hD' I), show (⨅ i ∈ _, D'' i) ≤ ψ ⁻¹ᵁ (⨅ i ∈ _, D' i) by
    rw [GlobalTheory.AbLaw.preimage_biInf]; exact iInf₂_mono fun i _ => hle i⟩

def pullCoef {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'}
    {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    CoefMap σ (covF s' D' hD') (covF s'' D'' hD'') where
  G := 𝟭 _
  α I := (pairPull w).α (op (pr D' hD' D'' hD'' hle I.unop))
  naturality {I J} f b := by
    have := (pairPull w).naturality (homOfLE (show pr D' hD' D'' hD'' hle J.unop ≤ pr D' hD' D'' hD'' hle I.unop from
      Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨(cov_mono D'' hD'') (leOfHom f.unop), (cov_mono D' hD') (leOfHom f.unop)⟩))).op b
    exact this
  smul I r b := (pairPull w).smul (op (pr D' hD' D'' hD'' hle I.unop)) r b

end Scheme

end GlobalTheory.CechPoset
