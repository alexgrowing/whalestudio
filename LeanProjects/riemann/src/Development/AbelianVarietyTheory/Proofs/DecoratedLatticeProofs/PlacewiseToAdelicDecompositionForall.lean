import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhereStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PlacesAdeles

variable {D : D7}

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem idAt_single_le {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  unfold idAt at ha ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  refine ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (by rw [h]; exact hv)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = w) ≤ idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

theorem idOff_le_single {P : Pl D → Prop} {v : Pl D} (hv : P v) : idOff D P ≤ idOff D (· = v) := by
  intro a ha
  unfold idOff at ha ⊢
  simp only [Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha ⟨u.1, by rw [hu]; exact hv⟩

theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  rw [mem_congGrp] at hg ⊢
  exact fun i j => h (hg i j)

theorem eq_zero_of_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem supp_mulVec (S : HSp D) (P : Pl D → Prop) (g : GA D S) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_of_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_mul {S : HSp D} {L : Lat S} {P : Pl D → Prop} {x x' : GA D S} (hx : Moves S x L L P)
    (hx' : Moves S x' L L P) : Moves S (x * x') L L P := by
  intro y hy
  rw [mt_mul, ← Matrix.mulVec_mulVec, hx' y hy]
  exact hx _ (supp_mulVec S P x' hy)

theorem moves_inv {S : HSp D} {L : Lat S} {P : Pl D → Prop} {x : GA D S} (hx : Moves S x L L P) :
    Moves S x⁻¹ L L P := by
  intro y hy
  have h1 := hx (mt S x⁻¹ *ᵥ y) (supp_mulVec S P _ hy)
  rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec] at h1
  exact h1.symm

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem latV_eq_ae : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := GlobalTheory.T.lattices_agree_almost_everywhere

end GlobalTheory.FinPl.PlacesAdeles

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.PlacesAdeles in

theorem placesToAdeles (D : D7) : PlacesToAdeles D := by
  classical
  intro S L P hL R h hyp
  obtain ⟨M, hM, hmove⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S L hL).1 h
  obtain ⟨T, hT⟩ := latV_eq_ae D S L M hL.1 hM.1
  have hfar : ∀ v, v ∉ T → Moves S h L L (· = v) := by
    intro v hv y hy
    have := hmove (· = v) y hy
    rwa [← hT v hv] at this
  have hloc : ∀ v, P v → ∃ r ∈ R, r ∈ grpAt S (· = v) ∧ Moves S (r⁻¹ * h) L L (· = v) := by
    intro v hv
    obtain ⟨hv', -, h', hh', hdec, r, hr, hrv, κ, hκ, hvk⟩ := hyp v hv
    refine ⟨r, hr, hrv, ?_⟩
    have : r⁻¹ * h = κ * h' := by rw [hdec, hvk]; group
    rw [this]
    exact moves_mul hκ.2 (moves_off hh')
  have key : ∀ T' : Finset (Pl D), (∀ v ∈ T', P v) → ∃ r ∈ R, r ∈ grpAt S P ∧
      (∀ v, v ∉ T' → r ∈ grpOff S (· = v)) ∧ ∀ v ∈ T', Moves S (r⁻¹ * h) L L (· = v) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, R.one_mem, (grpAt S P).one_mem, fun _ _ => Subgroup.one_mem _, by simp⟩
    | insert v₀ T' hv₀ ih =>
      intro hP
      obtain ⟨r, hr, hrP, hroff, hrm⟩ := ih (fun v hv => hP v (Finset.mem_insert_of_mem hv))
      have hP₀ : P v₀ := hP v₀ (Finset.mem_insert_self _ _)
      obtain ⟨r₀, hr₀, hr₀v, hm₀⟩ := hloc v₀ hP₀
      refine ⟨r * r₀, R.mul_mem hr hr₀, (grpAt S P).mul_mem hrP (congGrp_mono (idAt_single_le hP₀) hr₀v), ?_, ?_⟩
      · intro v hv
        have hne : v ≠ v₀ := fun e => hv (e ▸ Finset.mem_insert_self _ _)
        exact (grpOff S _).mul_mem (hroff v fun h => hv (Finset.mem_insert_of_mem h))
          (congGrp_mono (idAt_le_idOff hne) hr₀v)
      · intro v hv
        rw [_root_.mul_inv_rev, mul_assoc]
        rcases Finset.mem_insert.1 hv with rfl | hv
        · have hroff0 := hroff v hv₀
          have hcomm : r₀⁻¹ * r⁻¹ = r⁻¹ * r₀⁻¹ :=
            ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.1 _ (inv_mem hr₀v) _ (inv_mem hroff0)
          rw [← mul_assoc, hcomm, mul_assoc]
          exact moves_mul (moves_off (inv_mem hroff0)) hm₀
        · have hne : v ≠ v₀ := fun e => hv₀ (e ▸ hv)
          exact moves_mul (moves_off (inv_mem (congGrp_mono (idAt_le_idOff hne) hr₀v))) (hrm v hv)
  obtain ⟨r, hr, hrP, hroff, hrm⟩ := key (T.filter P) (fun v hv => (Finset.mem_filter.1 hv).2)
  have hall : ∀ v, P v → Moves S (r⁻¹ * h) L L (· = v) := by
    intro v hv
    by_cases hvT : v ∈ T
    · exact hrm v (Finset.mem_filter.2 ⟨hvT, hv⟩)
    · exact moves_mul (moves_off (inv_mem (hroff v (fun h => hvT (Finset.mem_filter.1 h).1)))) (hfar v hvT)
  obtain ⟨hdec, hcomm, -, hlat⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S
  obtain ⟨κ, hκ, g, hg, hx⟩ := hdec (r⁻¹ * h)
  have hκv : ∀ v, P v → Moves S κ L L (· = v) := by
    intro v hv
    have : κ = (r⁻¹ * h) * g⁻¹ := by rw [hx]; group
    rw [this]
    exact moves_mul (hall v hv) (moves_off (inv_mem (congGrp_mono (idOff_le_single hv) hg)))
  refine ⟨r, hr, hrP, g, hg, κ, ⟨hκ, ?_⟩, ?_⟩
  · intro y hy
    rw [hlat L y hL.1, hlat L _ hL.1]
    have hy' := supp_mulVec S P κ hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      rw [← Matrix.mulVec_smul]
      exact (hκv v hv _ (hey v e he)).1 (h2 v hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      have := h2 v hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hκv v hv _ (hey v e he)).2 this
  · calc h = r * (r⁻¹ * h) := by group
      _ = r * (κ * g) := by rw [hx]
      _ = r * g * κ := by rw [hcomm κ hκ g hg, mul_assoc]

theorem placesToAdeles_all : ∀ D : D7, PlacesToAdeles D := placesToAdeles

end GlobalTheory.FinPl
