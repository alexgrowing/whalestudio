import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkIdEqMonomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Surj
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOffOfIsOpen
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WGermB

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem projBCompl_mem {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}
    (y : projX P hP) : y ∈ projBCompl P D hP ↔ y ∉ (projB P D hP : Set (projX P hP)) := Iff.rfl

namespace WData

variable (w : WData P D hP)

theorem zero_bd (hD : IsMultiHomogIdeal D) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    (∀ h ∈ w.bd c, eval (w.coord c x) h = 0) ↔
      (fun q => eval (w.coord c x) (w.lift c q)) ∈ conePts D := by
  rw [← w.mem_projB_iff_lift hD c x hx, w.coord_of_mem c x hx]
  have h1 := (w.pres c.1 c.2).zero_bdIdeal_iff w.Zb x.1 hx x.2
  rw [w.support_Zb] at h1
  exact h1

theorem surj (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  exact w.surj' hD z hz hzD

theorem inj (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  exact w.inj' hD c c' x hx x' hx' hxD ho

theorem inv (hD : IsMultiHomogIdeal D) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c)
    (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D) (p : (k : K) → ι k)
    (hp : ∀ k, eval (w.coord c x) (w.lift c ⟨k, p k⟩) ≠ 0) :
    ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
      (F : Fin (w.pres c.1 c.2).n → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
        (∀ k, eval (w.coord c y) (w.lift c ⟨k, p k⟩) ≠ 0) ∧
        eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) q ≠ 0 ∧
        ∀ l, w.coord c y l * eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) q =
          eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) (F l) := by
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  have hxp : w.π.base x.1 ∈ (chartOpen hP p).1 := (w.mem_chartOpen_iff c x hx p).2 hp
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    (projBCompl_mem _).2 fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  haveI := w.isIso_off
  have hu : ∀ t : Γ(projX P hP, (chartOpen hP p).1), ∃ F : MvPolynomial (Σ k, ι k) ℂ,
      t = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) F := by
    intro t
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p t)
    exact ⟨F, by rw [← gammaChart_symm_mk, hF, RingEquiv.symm_apply_apply]⟩
  obtain ⟨O, hxO, hOle, q, F, -, hOF⟩ := exists_coord_inv (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl (projBCompl P D hP)
    (w.pres c.1 c.2) (chartOpen hP p).1 (chartOpen hP p).2 (chartCoord hP p) hu x.1 hx' hxp hxU x.2
  have hmem : ∀ y : w.M, y.1 ∈ O → y.1 ∈ (w.pres c.1 c.2).V ∧ w.π.base y.1 ∈ (chartOpen hP p).1 := by
    intro y hy
    have h := TopologicalSpace.Opens.mem_inf.1 (hOle hy)
    exact ⟨h.1, (TopologicalSpace.Opens.mem_inf.1 h.2).2⟩
  refine ⟨{y | y.1 ∈ O}, w.isOpen_zariski O, hxO, fun y hy => (hmem y hy).1, q, F, fun y hy => ?_⟩
  have hyV : y.1 ∈ (w.pres c.1 c.2).V := (hmem y hy).1
  have hyp : w.π.base y.1 ∈ (chartOpen hP p).1 := (hmem y hy).2
  have hval : (fun t => val (toSpecC hP) (chartCoord hP p t) (w.π.base y.1) hyp) =
      affCoord p (fun q => eval (w.coord c y) (w.lift c q)) :=
    funext fun t => w.val_chartCoord c y hyV p hyp t
  obtain ⟨h1, h2⟩ := hOF y.1 hyV hyp hy y.2
  have hc : w.coord c y = (w.pres c.1 c.2).coord y.1 hyV := w.coord_of_mem c y hyV
  refine ⟨(w.mem_chartOpen_iff c y hyV p).1 hyp, ?_, fun l => ?_⟩
  · rw [← hval]; exact h1
  · rw [← hval, hc]; exact h2 l

theorem exists_sncData_w {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∃ S : SncData (w.pres c.1 c.2).K (w.bd c) (w.coord c x) e w.rc,
      (∀ l ∈ S.J, ∃ k, S.σ l = some k ∧ ∃ hx' : x.1 ∈ (w.pres c.1 c.2).V,
        IsBranch (w.Zb.support : Set w.W) ((w.pres c.1 c.2).secHom (S.r l)) x.1
          (w.compEquiv k)) ∧
      ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∀ k,
        w.comp k ∩ O = {y ∈ O | ∃ l, S.σ l = some k ∧ eval (w.coord c y) (S.r l) = 0} := by
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  obtain ⟨S, hS, O, hxO, hOV, hO⟩ :=
    exists_sncData w.snc_Zb (w.pres c.1 c.2) w.compEquiv e x.1 hx' x.2 (he x)
  rw [w.coord_of_mem c x hx]
  refine ⟨S, fun l hl => ?_, {y | y.1 ∈ O}, w.isOpen_zariski O, hxO, fun y hy => hOV hy,
    fun k => ?_⟩
  · obtain ⟨k, hk, hb⟩ := hS l hl
    exact ⟨k, hk, hx', hb⟩
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyk, hyO⟩
      have hyV : y.1 ∈ (w.pres c.1 c.2).V := hOV hyO
      refine ⟨hyO, ?_⟩
      rw [w.coord_of_mem c y hyV]
      exact (hO k y.1 hyV hyO y.2).1 hyk
    · rintro ⟨hyO, hl⟩
      have hyV : y.1 ∈ (w.pres c.1 c.2).V := hOV hyO
      rw [w.coord_of_mem c y hyV] at hl
      exact ⟨(hO k y.1 hyV hyO y.2).2 hl, hyO⟩

def sncAt {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx)
    (x : w.M) (hx : x ∈ w.src c) : SncData (w.pres c.1 c.2).K (w.bd c) (w.coord c x) e w.rc :=
  Classical.choose (w.exists_sncData_w he c x hx)

theorem sncAt_branch {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∀ l ∈ (w.sncAt he c x hx).J, ∃ k, (w.sncAt he c x hx).σ l = some k ∧
      ∃ hx' : x.1 ∈ (w.pres c.1 c.2).V,
        IsBranch (w.Zb.support : Set w.W) ((w.pres c.1 c.2).secHom ((w.sncAt he c x hx).r l)) x.1
          (w.compEquiv k) :=
  (Classical.choose_spec (w.exists_sncData_w he c x hx)).1

theorem comp_eq {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx)
    (x : w.M) (hx : x ∈ w.src c) :
    ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∀ k,
      w.comp k ∩ O = {y ∈ O | ∃ l, (w.sncAt he c x hx).σ l = some k ∧
        eval (w.coord c y) ((w.sncAt he c x hx).r l) = 0} :=
  (Classical.choose_spec (w.exists_sncData_w he c x hx)).2

theorem exists_divIdeal (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ G : w.W.IdealSheafData, FinalTheorems.EffCartier G ∧ (G.support : Set w.W) ⊆ w.Zb.support ∧
      ∀ (c : w.Idx) (x : w.M) (hx : x.1 ∈ (w.pres c.1 c.2).V),
        FinalTheorems.stalkId G x.1 = Ideal.span {w.W.presheaf.germ (w.pres c.1 c.2).V x.1 hx
          ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))} := by
  obtain ⟨G, hG⟩ := exists_idealSheaf_of_locGen (fun c : w.Idx => (w.pres c.1 c.2).V)
    w.exists_mem_pres_V (fun c => (w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))
    (fun c c' x hx hx' => w.germ_lift_ratio f a hf c c' x hx hx')
  refine ⟨G, effCartier_of_stalkId G (fun x => ?_), fun x hxG => ?_, fun c x hx => hG c x.1 hx⟩
  · obtain ⟨c, hc⟩ := w.exists_mem_pres_V x
    haveI := w.regular x
    haveI : IsDomain (w.W.presheaf.stalk x) := isDomain_of_isRegularLocalRing
    exact ⟨_, mem_nonZeroDivisors_of_ne_zero (w.germ_lift_ne_zero hD hcomp f a hf hzero c x hc),
      hG c x hc⟩
  · by_contra hxZ
    rw [w.support_Zb] at hxZ
    obtain ⟨c, hc⟩ := w.exists_mem_pres_V x
    have hu := w.germ_lift_isUnit hD f a hf hzero c x hc hxZ
    rw [mem_support_iff_stalkId, hG c x hc, Ideal.span_singleton_eq_top.2 hu] at hxG
    exact hxG rfl

theorem mult {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (hD : IsMultiHomogIdeal D) (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a) (hfP : f ∉ P)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ m : Fin w.rc → ℕ, ∀ c (x : w.M) (hx : x ∈ w.src c),
      ∃ u : locRing (w.pres c.1 c.2).K (w.coord c x), IsUnit u ∧
        algebraMap _ (locRing (w.pres c.1 c.2).K (w.coord c x)) (bind₁ (w.lift c) f) =
          u * ∏ l ∈ (w.sncAt he c x hx).J,
            algebraMap _ (locRing (w.pres c.1 c.2).K (w.coord c x)) ((w.sncAt he c x hx).r l) ^
              ((w.sncAt he c x hx).σ l).elim 0 m := by
  obtain ⟨G, hG, hGZ, hGx⟩ := w.exists_divIdeal hD hcomp f a hf hzero
  refine ⟨fun k => ordAlong G (w.compEquiv k), fun c x hx => ?_⟩
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  haveI := w.regular x.1
  exact monomial_chart hG hGZ (w.pres c.1 c.2) w.compEquiv e x.1 hx' x.2 (he x)
    (w.coord_of_mem c x hx).symm (w.sncAt he c x hx)
    (fun l hl => by
      obtain ⟨k, hk, _, hb⟩ := w.sncAt_branch he c x hx l hl
      exact ⟨k, hk, hb⟩) _ (hGx c x hx')

end WData

end

end ReciprocityTheory.AnForm.R
