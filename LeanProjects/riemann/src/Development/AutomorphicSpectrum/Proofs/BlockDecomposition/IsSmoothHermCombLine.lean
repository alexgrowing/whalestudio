import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

section Line

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zpow_sum_eq_prod {α : Type} (s : Finset α) {x : ℝ} (hx : x ≠ 0) (f : α → ℤ) :
    x ^ (∑ o ∈ s, f o) = ∏ o ∈ s, x ^ f o := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

open Classical in

def combLine {κ : Type} [Fintype κ] (A : κ → HermLine ι) (a : κ → ℤ) : HermLine ι where
  a := ∑ o, a o • (A o).a
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then ∏ o, (A o).h z ^ a o else 0
  pos z hz := by
    rw [if_pos hz]
    exact Finset.prod_pos fun o _ => zpow_pos ((A o).pos z hz) _
  smul c z hc := by
    have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
    have e : ∀ k, ‖c k‖ ^ (∑ o, a o • (A o).a) k = ∏ o, (‖c k‖ ^ (A o).a k) ^ a o := fun k => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [zpow_sum_eq_prod _ (hn k)]
      exact Finset.prod_congr rfl fun o _ => by rw [mul_comm, zpow_mul]
    have hz : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 :=
      forall_congr' fun k => exists_congr fun i => by simp [hc k]
    by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · rw [if_pos (hz.2 h), if_pos h]
      simp only [e, (A _).smul c z hc, mul_zpow, Finset.prod_mul_distrib]
      rw [Finset.prod_comm]
      simp only [Finset.prod_zpow]
    · rw [if_neg (fun h' => h (hz.1 h')), if_neg h, mul_zero]

end Line

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Pol (n : Fin (m + 1) → ℕ) := MRing (Bk n)

def dehomog (c : ∀ k, Bk n k) : Pol n →+* Γ(MP ℤ m n, mchart c) :=
  eval₂Hom (Int.castRingHom _) fun q => resG _ (mchart_le c q.1) (pullRatio (prB n q.1) _ (c q.1) le_rfl q.2)

def RepBy (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ) : Prop :=
  (∀ i j c,
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
      Semi.res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
  (∀ i c c',
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
  ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
    A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
        Real.exp ((M.φ σ₀).φ i y / 2)

theorem isHermRep_iff (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) : IsHermRep M A ↔ ∃ u, RepBy M A u := Iff.rfl

section Rat

variable {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n)

def fnAt (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (s : Pol n) : X.functionField :=
  fnOf _ h (i.app _ (dehomog c s))

variable {i}

def RatOf (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (r : (M.restr i).B.ι → X.functionFieldˣ) (f g : Pol n) : Prop :=
  ∃ u, RepBy M A u ∧ ∀ (b : M.B.ι) (c : ∀ k, Bk n k) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c)
    (hb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c)),
    fnOf _ hb (i.app _ (u b c).val) * (r fun _ => b : X.functionField) * fnAt i c hc g = fnAt i c hc f

end Rat

def cycVal (II : IntersectionSystem) (A : HermLine (Bk n)) (d : ℕ) (W : Ideal (Pol n)) : ℝ := by
  classical
  exact if IsHorizontal W then II (Fin (m + 1)) (Bk n) W d (fun _ => A)
    else (geoNum d W (fun _ => A.a) : ℝ) * Real.log (charOf W)

open ReciprocityTheory.ChartRestriction.G.Geo (pot IsMultiProjPrime IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK (ResKStatement)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (RatRStatement)

def ExistsRead : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), GlobalTheory.ArithmeticHeightTower.IsTwB M →
  ∃ A : HermLine (Bk n), IsSmoothHerm A ∧ IsHermRep M A ∧ ∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = 0

def ReadComb : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (κ : Type) [Fintype κ] (M : κ → HermLB (mpStr ℤ m n))
  (A : κ → HermLine (Bk n)), (∀ o, IsHermRep (M o) (A o)) → ∀ a : κ → ℤ, IsHermRep (comb M a) (combLine A a)

def PtDict : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (j : Z ⟶ MP ℤ m n)
  [IsClosedImmersion j] (d : ℕ), topologicalKrullDim Z = d →
    IsMultiProjPrime (ptIdeal (j (genericPoint Z))) ∧
    (IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤)) ∧
    (IsHorizontal (ptIdeal (j (genericPoint Z))) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (j (genericPoint Z))) d) ∧
    (¬ IsHorizontal (ptIdeal (j (genericPoint Z))) → (charOf (ptIdeal (j (genericPoint Z)))).Prime ∧
      ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0)

def CodimOne : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), GlobalTheory.IsArithVar p D → ∀ z : X,
  Order.coheight z = 1 → topologicalKrullDim (closure ({z} : Set X)) = (D : ℕ)

def ExistsRat : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (_ : IsHermRep M A)
  (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ),
    IsRatSec (M.restr i).B r → ∃ f g : Pol n, IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g ∧ RatOf M A r f g

def CycleOfRat : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (_ : IsHermRep M A)
  (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → ∀ (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g → ∀ u : Ideal (Pol n) → ℝ,
      ∑ᶠ z, (((M.restr i).div hr).mult z : ℝ) * u (ptIdeal (i z)) =
        (∑ᶠ W ∈ divSupp (ptIdeal (i (genericPoint X))) f,
          (multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {f}) W : ℝ) * u W) -
        ∑ᶠ W ∈ divSupp (ptIdeal (i (genericPoint X))) g,
          (multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {g}) W : ℝ) * u W

def ArchIntEq : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (N M : HermLB (mpStr ℤ m n)) (B A : HermLine (Bk n))
  (_ : IsHermRep N B) (_ : IsHermRep M A) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → IsSmoothHerm B → IsSmoothHerm A →
    ∀ (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r) (f g : Pol n),
      IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
        (N.restr i).archInt (M.restr i) D hr =
          ptsIntegral (ptIdeal (i (genericPoint X))) (pot fun _ : Fin D => B) (logNormRat A f g)

def ArchIntegrableOn : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (N M : HermLB (mpStr ℤ m n))
  (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → ∀ (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r),
      (N.restr i).ArchIntegrable (M.restr i) D hr

def VertEq : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (_ : IsHermRep M A)
  (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (Z : Scheme.{0}) [IsIntegral Z] (j : Z ⟶ X)
  [IsClosedImmersion j] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)] (d : ℕ), topologicalKrullDim Z = d →
    topSelfIntersection (ZMod p) ((M.B.pull i).pull j) d = geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a)

def PtLen : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X),
  topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ,
    (geoNum 0 (ptIdeal (i z)) a : ℝ) * Real.log (charOf (ptIdeal (i z))) = Real.log (Nat.card (X.residueField z))

def CurveInt : Prop := ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℤ), GlobalTheory.IsArithVar q 0 → ∀ (L M : HermLB q)
  (r : M.B.ι → Z.functionFieldˣ) (hr : IsRatSec M.B r),
    L.ArchIntegrable M 0 hr ∧ L.archInt M 0 hr = ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y

def HeightEq (II : IntersectionSystem) : Prop := ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (N : HermLB (mpStr ℤ m n))
  (A : HermLine (Bk n)) (_ : IsHermRep N A), IsSmoothHerm A → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
  (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (h : X → ℝ), (N.restr i).IsArithHeight h → ∀ (z : X) (d : ℕ),
    topologicalKrullDim (closure ({z} : Set X)) = d → h z = cycVal II A d (ptIdeal (i z))

def Polar : Prop := ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
  (F : (e : ℕ) → (Fin e → HermLine ι) → ℝ) (D : ℕ) (κ : Type) [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι),
    IsSmoothHerm A₀ → (∀ j, IsSmoothHerm (A j)) → (∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A₀.h z = 0) →
    (∀ j z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (A j).h z = 0) →
    (∀ (L : Fin (D + 1) → HermLine ι) (s : Equiv.Perm (Fin (D + 1))), (∀ j, IsSmoothHerm (L j)) → F (D + 1) (L ∘ s) = F (D + 1) L) →
    (∀ (L : Fin (D + 1) → HermLine ι) (j : Fin (D + 1)) (B C : HermLine ι), (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
      IsSmoothHerm C → F (D + 1) (Function.update L j (B.tensor C)) =
        F (D + 1) (Function.update L j B) + F (D + 1) (Function.update L j C)) →
    ∀ Φ : MvPolynomial (Option κ) ℝ →ₗ[ℝ] ℝ,
      (∀ a : Option κ → ℤ, Φ (lin (fun o => (a o : ℝ)) ^ (D + 1)) =
        F (D + 1) fun _ => combLine (fun o : Option κ => o.elim A₀ A) a) →
      ∀ n : κ → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        F (D + 1) (Fin.snoc (fun _ : Fin D => combLine A n) A₀)

theorem isSmoothHerm_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]
    {A : κ → HermLine ι} (h : ∀ o, IsSmoothHerm (A o)) (a : κ → ℤ) : IsSmoothHerm (combLine A a) := by
  refine ContDiffOn.congr (f := fun z => ∏ o, (A o).h z ^ a o) ?_ fun z hz => if_pos hz
  refine contDiffOn_prod fun o _ => ?_
  have hp : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, (A o).h z ≠ 0 := fun z hz => ((A o).pos z hz).ne'
  cases a o with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using (h o).pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact ((h o).pow (k + 1)).inv fun z hz => pow_ne_zero _ (hp z hz)

theorem dim_closure_generic (X : Scheme.{0}) [IsIntegral X] :
    topologicalKrullDim (closure ({genericPoint X} : Set X)) = topologicalKrullDim X := by
  rw [genericPoint_closure]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

theorem mixZ_of (h₁ : ExistsRead) (h₂ : ReadComb) (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat)
    (h₇ : ArchIntEq) (h₈ : ArchIntegrableOn) (h₉ : Polar) (hR : RatRStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (hH : HeightEq II) : GlobalTheory.ArithmeticHeightTower.MixZ := by
  intro m n X _ _ i _ D hX ι _ M₀ M t₀ tM Φ hΦ nn h hh r hr
  obtain ⟨A₀, s₀, R₀, c₀⟩ := h₁ m n M₀ t₀
  choose A sA RA cA using fun j => h₁ m n (M j) (tM j)
  let M' : Option ι → HermLB (mpStr ℤ m n) := fun o => o.elim M₀ M
  let A' : Option ι → HermLine (Bk n) := fun o => o.elim A₀ A
  have sA' : ∀ o, IsSmoothHerm (A' o) := by
    rintro (_ | j)
    exacts [s₀, sA j]
  have RA' : ∀ o, IsHermRep (M' o) (A' o) := by
    rintro (_ | j)
    exacts [R₀, RA j]
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n X i (D + 1) hX.dim_eq
  have hhor : IsHorizontal (ptIdeal (i (genericPoint X))) := hp₃.2 hC
  have hP := hp₄ hhor
  have diag : ∀ a : Option ι → ℤ, Φ (lin (fun o => (a o : ℝ)) ^ (D + 1)) =
      II (Fin (m + 1)) (Bk n) (ptIdeal (i (genericPoint X))) (D + 1) fun _ => combLine A' a := by
    intro a
    obtain ⟨h', H', e⟩ := hΦ.1 a
    have eL : (fun o : Option ι => o.elim (M₀.restr i) fun j => (M j).restr i) = fun o => (M' o).restr i := by
      funext o
      cases o <;> rfl
    rw [eL] at H'
    have H'' := (isometric_comb_pull M' a i rfl).isArithHeight hX H'
    have Rc := h₂ m n _ M' A' RA' a
    have e₂ := hH m n _ _ Rc (isSmoothHerm_combLine sA' a) X i h' H'' (genericPoint X) (D + 1)
      ((dim_closure_generic X).trans hX.dim_eq)
    rw [← e, e₂, cycVal]
    exact if_pos hhor
  have RN := h₂ m n ι M A RA nn
  have sB := isSmoothHerm_combLine sA nn
  have iso := isometric_comb_pull (fun j => M j) nn i rfl
  have hh' := iso.isArithHeight hX hh
  have hI := h₈ m n (comb M nn) M₀ X i D hX r hr
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n M₀ A₀ R₀ X i r hr
  have hcyc := h₆ m n M₀ A₀ R₀ X i D hX r hr f g hfg hrat (cycVal II (combLine A nn) D)
  have hint := h₇ m n (comb M nn) M₀ _ A₀ RN R₀ X i D hX sB s₀ r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ D (fun _ => combLine A nn) A₀ f g hP (fun _ => sB) s₀ hfg
  have hpol := h₉ _ (Bk n) (fun e L => II _ (Bk n) (ptIdeal (i (genericPoint X))) e L) D ι A₀ A s₀ sA c₀ cA
    (fun L s hs => (hII.1 _ _).1 _ _ L s hP hs)
    (fun L j B C hs hB hC => hII.2.1 _ _ _ _ L j B C hP hs hB hC) Φ diag nn
  refine ⟨fun σ => ?_, ?_⟩
  · rw [iso.chernIntegrableOn_eq σ D]
    exact hI σ
  · have e₁ : (comb (fun j => (M j).restr i) nn).archInt (M₀.restr i) D hr =
        ((comb M nn).restr i).archInt (M₀.restr i) D hr := by
      simp only [HermLB.archInt, iso.chernInt_eq]
    have e₂ : ∑ᶠ z, (((M₀.restr i).div hr).mult z : ℝ) * h z =
        ∑ᶠ z, (((M₀.restr i).div hr).mult z : ℝ) * cycVal II (combLine A nn) D (ptIdeal (i z)) := by
      refine finsum_congr fun z => ?_
      by_cases hz : ((M₀.restr i).div hr).mult z = 0
      · simp [hz]
      · rw [hH m n _ _ RN sB X i h hh' z D (h₄ X _ D hX z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]
    rw [hpol, hrr, e₁, hint, e₂, hcyc]
    rfl

end GlobalTheory.CompanionTheory.MixZ
