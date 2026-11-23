import ReciprocityTheory.AnalyticForms.RegularLocalRings.NeZeroOfSpanEqMaximalIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem jacobsonSpace_W : JacobsonSpace w.W := by
  have := w.lft
  exact LocallyOfFiniteType.jacobsonSpace (w.π ≫ toSpecC hP)

theorem exists_mem_pres_V (x : w.W) : ∃ c : w.Idx, x ∈ (w.pres c.1 c.2).V := by
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base x)
  have hx : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hp
  rw [← w.iSup_pres p] at hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨⟨p, i⟩, hi⟩

theorem exists_closed_off_of_isOpen (N : Set w.W) (hN : IsOpen N) (hne : N.Nonempty) :
    ∃ x' : w.M, x'.1 ∈ N ∧ w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) := by
  haveI := w.jacobsonSpace_W
  obtain ⟨x0, hx0N, hx0c⟩ := nonempty_inter_closedPoints hne hN.isLocallyClosed
  obtain ⟨c, hc⟩ := w.exists_mem_pres_V x0
  haveI := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x0 hc hx0c).mp (w.regular x0)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x0 hc)
  obtain ⟨T, hT⟩ := (w.pres c.1 c.2).exists_basicOpen_cover ⟨N, hN⟩
  obtain ⟨G, hGT, hx0G⟩ := (hT x0 hc).mp hx0N
  have hG0 : eval ((w.pres c.1 c.2).coord x0 hc) G ≠ 0 := by
    have := (w.mem_basicOpen_iff c ⟨x0, hx0c⟩ hc G).mp hx0G
    rwa [w.coord_of_mem c ⟨x0, hx0c⟩ hc] at this
  obtain ⟨x', hx'V, -, hx'B, hx'G⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) ⟨x0, hx0c⟩ hc 𝔮 h𝔮min h𝔮x G hG0
  refine ⟨x', ?_, hx'B⟩
  have hmem : x'.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom G) := by
    rw [w.mem_basicOpen_iff c x' hx'V G, w.coord_of_mem c x' hx'V]; exact hx'G
  exact (hT x'.1 hx'V).mpr ⟨G, hGT, hmem⟩

theorem eval_bind_lift_ne_zero (hD : IsMultiHomogIdeal D) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c)
    (hxB : w.π.base x.1 ∉ (projB P D hP : Set (projX P hP))) :
    eval (w.coord c x) (bind₁ (w.lift c) f) ≠ 0 := by
  have h1 : eval (w.coord c x) (bind₁ (w.lift c) f) =
      eval (fun q => eval (w.coord c x) (w.lift c q)) f := by
    show aeval (w.coord c x) (bind₁ (w.lift c) f) = aeval (fun q => aeval (w.coord c x) (w.lift c q)) f
    exact aeval_bind₁ _ _ _
  rw [h1]
  intro h0
  exact hxB ((w.mem_projB_iff_lift hD c x hx).mpr (hzero _ (w.lift_mem c x hx) h0))

theorem germ_lift_ne_zero (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V) :
    w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) ≠ 0 := by
  intro h0
  have h0' : w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) =
      w.W.presheaf.germ _ x hx 0 := by rw [h0, map_zero]
  obtain ⟨O, hxO, iO, iO', hO⟩ := TopCat.Presheaf.germ_eq w.W.presheaf x hx hx _ _ h0'
  obtain ⟨x', hx'O, hx'B⟩ := w.exists_closed_off_of_isOpen O O.isOpen ⟨x, hxO⟩
  have hx'V : x'.1 ∈ (w.pres c.1 c.2).V := iO.le hx'O
  have hnot : x'.1 ∉ w.W.basicOpen ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) := by
    intro hm
    have hres : x'.1 ∈ w.W.basicOpen
        (w.W.presheaf.map iO.op ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))) := by
      rw [Scheme.basicOpen_res]; exact ⟨hx'O, hm⟩
    rw [hO, map_zero, Scheme.basicOpen_zero] at hres
    exact hres
  apply w.eval_bind_lift_ne_zero hD f hzero c x' hx'V hx'B
  by_contra hne
  exact hnot ((w.mem_basicOpen_iff c x' hx'V _).mpr hne)

theorem germ_lift_isUnit (hD : IsMultiHomogIdeal D)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V)
    (hxB : w.π.base x ∉ (projB P D hP : Set (projX P hP))) :
    IsUnit (w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))) := by
  haveI := w.jacobsonSpace_W
  refine (w.W.mem_basicOpen _ x hx).mp ?_
  by_contra hxs
  let U : w.W.Opens := (w.pres c.1 c.2).V ⊓ w.π ⁻¹ᵁ projBCompl P D hP
  have hZ : (closure {x} ∩ (U : Set w.W)).Nonempty := ⟨x, subset_closure rfl, hx, hxB⟩
  have hZlc : IsLocallyClosed (closure {x} ∩ (U : Set w.W)) :=
    isClosed_closure.isLocallyClosed.inter U.isOpen.isLocallyClosed
  obtain ⟨y, ⟨hyx, hyV, hyB⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
  have hys : y ∉ w.W.basicOpen ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) := by
    intro hm
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hyx _ (w.W.basicOpen _).isOpen hm
    rw [Set.mem_singleton_iff.mp hz] at hzU
    exact hxs hzU
  apply w.eval_bind_lift_ne_zero hD f hzero c ⟨y, hyc⟩ hyV hyB
  by_contra hne
  exact hys ((w.mem_basicOpen_iff c ⟨y, hyc⟩ hyV _).mpr hne)

end WData

end ReciprocityTheory.AnForm.R
