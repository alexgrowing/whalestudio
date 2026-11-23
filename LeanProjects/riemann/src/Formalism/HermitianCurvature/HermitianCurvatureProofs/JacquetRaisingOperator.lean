import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.JA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section expand

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def tsOf (u : ℂ) (c : Fin r → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin r)) :
    List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
  List.ofFn fun j : Fin r => (u - ((j : ℕ) : ℂ), C3.xR k r r le_rfl (σ j), c j)

def coefC (c : Fin r → Fin (2 * r + k + 1)) (g : Mat k r) : ℂ :=
  if StrictMono c then
    (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det
  else 0

def wsum (u : ℂ) (c : Fin r → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin r)) (f : Mat k r → E) (g : Mat k r) : E :=
  ((expand k r (tsOf u c σ)).map fun cw => cw.1 • Rw cw.2 f g).sum

theorem tsOf_length (u : ℂ) (c : Fin r → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin r)) :
    (tsOf (k := k) u c σ).length = r := by
  simp [tsOf]

theorem aa_expand (u : ℂ) (f : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hf : Loc (r : ℕ∞) f g) :
    C3.AAop k r r le_rfl u f g =
      ∑ c, coefC c g • ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) • wsum u c σ f g := by
  unfold C3.AAop
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold coefC
  split_ifs with hc
  · congr 1
    simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hl : Loc ((tsOf (k := k) u c σ).length : ℕ∞) f g := by rw [tsOf_length]; exact hf
    rw [wsum, ← expand_eq (tsOf u c σ) f g hg hl]
    simp only [foldT, tsOf, List.map_ofFn]
    rfl
  · simp

theorem rw_clm (L : E →L[ℂ] E) : ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) →
    ∀ (f : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (w.length : ℕ∞) f g →
      Rw w (fun x => L (f x)) g = L (Rw w f g)
  | [], _, _, _, _, _ => rfl
  | X :: w, hw, f, g, hg, hf => by
    obtain ⟨U, hU, hgU, hUloc⟩ := loc_spread hf
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (by simp [hY])
    have hagree : ∀ x ∈ U, x ∈ GV k r → Rw w (fun x => L (f x)) x = L (Rw w f x) := fun x hx hxG =>
      rw_clm L w hw' f x hxG (loc_mono (by simp) (hUloc x hx))
    show RdV X (Rw w (fun x => L (f x))) g = L (RdV X (Rw w f) g)
    rw [rdV_congr hU hgU hg (hw X (by simp)) hagree]
    have hl : Loc (1 : ℕ∞) (Rw w f) g := by
      have := loc_Rw (N := w.length + 1) (by simpa using hf) w hw' 1 (by omega)
      simpa using this
    have hd := loc_hasDerivAt le_rfl hl hg (hw X (by simp))
    exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv

theorem wsum_clm (L : E →L[ℂ] E) (u : ℂ) (c : Fin r → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin r))
    (f : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hf : Loc (r : ℕ∞) f g) :
    wsum u c σ (fun x => L (f x)) g = L (wsum u c σ f g) := by
  unfold wsum
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  have hw := expand_words (tsOf u c σ) cw hcw
  simp only [Function.comp_apply, map_smul]
  rw [rw_clm L cw.2 (fun X hX => (hw.1 X hX).1) f g hg
    (loc_mono (by rw [tsOf_length] at hw; exact_mod_cast hw.2) hf)]

theorem aa_clm (L : E →L[ℂ] E) (u : ℂ) (f : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r)
    (hf : Loc (r : ℕ∞) f g) (hLf : Loc (r : ℕ∞) (fun x => L (f x)) g) :
    C3.AAop k r r le_rfl u (fun x => L (f x)) g = L (C3.AAop k r r le_rfl u f g) := by
  rw [aa_expand u _ g hg hLf, aa_expand u f g hg hf, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, wsum_clm L u c σ f g hg hf]

end expand

section rho

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def postL (A₁ : Wp →L[ℂ] Wp) (A₂ : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A₁.comp (A.comp A₂)
      map_add' := fun A B => by ext v; simp
      map_smul' := fun c A => by ext v; simp }

theorem postL_apply (A₁ : Wp →L[ℂ] Wp) (A₂ : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    postL A₁ A₂ A = A₁.comp (A.comp A₂) := rfl

def mulLR (s s' : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ s).comp (LinearMap.mulRight ℝ s'))

theorem mulLR_apply (s s' x : Mat k r) : mulLR s s' x = s * x * s' := by
  simp [mulLR, Matrix.mul_assoc]

theorem loc_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E}
    (hf : CkOn ⊤ (GV k r) f) {g : Mat k r} (hg : g ∈ GV k r) (m : ℕ∞) : Loc m f g := by
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g hg
  exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx hxG⟩

theorem loc_transl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mat k r → E}
    {s s' g : Mat k r} (hs : s ∈ GV k r) (hs' : s' ∈ GV k r) (h : Loc m f (s * g * s')) :
    Loc m (fun x => f (s * x * s')) g := by
  obtain ⟨U, f', hU, hgU, hc, he⟩ := h
  refine ⟨(mulLR s s') ⁻¹' U, fun x => f' (mulLR s s' x), hU.preimage (mulLR s s').continuous,
    by simpa [mulLR_apply] using hgU, hc.comp (mulLR s s').contDiff.contDiffOn (fun x hx => hx),
    fun x hx hxG => ?_⟩
  have hx' : s * x * s' ∈ U := by simpa [Set.mem_preimage, mulLR_apply] using hx
  simp only [mulLR_apply]
  exact he _ hx' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hxG) hs')

theorem loc_post {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mat k r → E}
    {g : Mat k r} (L : E →L[ℂ] E) (h : Loc m f g) : Loc m (fun x => L (f x)) g := by
  obtain ⟨U, f', hU, hgU, hc, he⟩ := h
  exact ⟨U, fun x => L (f' x), hU, hgU, (L.restrictScalars ℝ).contDiff.comp_contDiffOn hc,
    fun x hx hxG => by simp only [he x hx hxG]⟩

theorem rho_aa (Bs : B.RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) (u : ℂ)
    {p : SS k r} (hp : Bs.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    rho Bs p (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (rho Bs p F) g := by
  set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef
  set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def
  have hs : s ∈ Sset k r Bs.z :=
    ⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩
  have hs' : s' ∈ Sset k r Bs.z' :=
    (Formalism.QuantumDeterminants.sGroup k r Bs.z' Bs.z'_mem).2.1 _ ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw Bs.z', _, hp.2.2.2, by simp⟩ _
      ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩
  have hsG := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs
  have hs'G := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs'
  have hsgs : ∀ y : Mat k r, sgs p y = s * y * s' := by
    intro y; simp [sgs, hsdef, hs'def, Matrix.mul_assoc]
  have hSm : SmoothOnH (Hpk k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hgU, hc, fun x hx hxG => he x hx hxG⟩
  have hX0 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 F Bs.z_mem Bs.z'_mem hSm
    s hs s' hs' g hg).1
  set L := postL (Bs.π (Matrix.of p.1.1)) (Bs.π' (Matrix.of p.2.1)⁻¹) with hL
  have e1 : rho Bs p (C3.AAop k r r le_rfl u F) g = L (C3.AAop k r r le_rfl u F (s * g * s')) := by
    simp only [rho, hsgs, hL, postL_apply]
  have e2 : rho Bs p F = fun x => L (F (s * x * s')) := by
    funext x; simp only [rho, hsgs, hL, postL_apply]
  have hloc : Loc (r : ℕ∞) (fun x => F (s * x * s')) g :=
    loc_transl hsG hs'G (loc_of_ck hF (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hg) hs'G) _)
  rw [e1, e2, ← hX0, aa_clm L u _ g hg hloc (loc_post L hloc)]

end rho

section main

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem loc_rho (Bs : B.RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {p : SS k r} (hp : Bs.inSS p) {g : Mat k r} (hg : g ∈ GV k r) (m : ℕ∞) : Loc m (rho Bs p F) g := by
  set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef
  set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def
  have hs : s ∈ Sset k r Bs.z :=
    ⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩
  have hs' : s' ∈ Sset k r Bs.z' :=
    (Formalism.QuantumDeterminants.sGroup k r Bs.z' Bs.z'_mem).2.1 _ ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw Bs.z', _, hp.2.2.2, by simp⟩ _
      ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩
  have hsG := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs
  have hs'G := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs'
  have hsgs : ∀ y : Mat k r, sgs p y = s * y * s' := by
    intro y; simp [sgs, hsdef, hs'def, Matrix.mul_assoc]
  set L := postL (Bs.π (Matrix.of p.1.1)) (Bs.π' (Matrix.of p.2.1)⁻¹) with hL
  have e2 : rho Bs p F = fun x => L (F (s * x * s')) := by
    funext x; simp only [rho, hsgs, hL, postL_apply]
  rw [e2]
  exact loc_post L (loc_transl hsG hs'G (loc_of_ck hF (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hg) hs'G) _))

theorem smul_list_sum {ι V : Type*} [AddCommGroup V] [Module ℂ V] (a : ℂ) (L : List ι) (f : ι → V) :
    a • (L.map f).sum = (L.map fun i => a • f i).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [smul_add, ih]

theorem int_list {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure (SS k r)}
    (L : List (ℂ × ι)) (φ : ℂ × ι → SS k r → V) (val : ℂ × ι → V)
    (h : ∀ cw ∈ L, Integrable (φ cw) μ ∧ val cw = ∫ p, φ cw p ∂μ) :
    Integrable (fun p => (L.map fun cw => cw.1 • φ cw p).sum) μ ∧
      ∫ p, (L.map fun cw => cw.1 • φ cw p).sum ∂μ = (L.map fun cw => cw.1 • val cw).sum := by
  induction L with
  | nil => simp
  | cons cw L ih =>
    obtain ⟨hI, hv⟩ := h cw (by simp)
    obtain ⟨hI', hv'⟩ := ih (fun c hc => h c (by simp [hc]))
    simp only [List.map_cons, List.sum_cons]
    have h1 : Integrable (fun p => cw.1 • φ cw p) μ := hI.smul cw.1
    refine ⟨h1.add hI', ?_⟩
    rw [integral_add h1 hI', integral_smul, hv', hv]

end main

end Formalism.FourierDecayAlt.P.PBN.JA

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBN.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jacquet_raising_operator : PBN.JAAop := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F u hF g hg
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  set A : ℝ := 12 * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hA
  have hT : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A r := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of k r r A le_rfl
  have hFA : InCC A r F := hn.2.1 A r
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq Bs A r F hT hFA
  have hCk : CkOn (r : ℕ∞) (GV k r) F := hFA.choose_spec.1
  have hgG : g ∈ GV k r := hg.1

  have key : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ r →
      Integrable (fun p => xiP Bs p • Rw v (rho Bs p F) g) Bs.μSS ∧
      Rw v (JF Bs F) g = ∫ p, xiP Bs p • Rw v (rho Bs p F) g ∂Bs.μSS := by
    intro v hvu hvl
    obtain ⟨hI, hE⟩ := hW.2 [] v (by simp) hvu (by simpa using hvl) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP Bs p • rho Bs p (dLR [] (v.map (AdR p)) F) g) =ᵐ[Bs.μSS]
        fun p => xiP Bs p • Rw v (rho Bs p F) g := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have := Formalism.FourierDecayAlt.P.rewrite_rho_action k r Wp Wq Bs r F p hp hCk [] v (by simp) (fun X hX => (hvu X hX).1)
        (by simpa using hvl) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    refine ⟨hI.congr hae, ?_⟩
    rw [← integral_congr_ae hae]
    exact hE

  have hIc : ∀ (c : Fin r → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin r)),
      Integrable (fun p => ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum)
        Bs.μSS ∧
      ∫ p, ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum ∂Bs.μSS =
        wsum u c σ (JF Bs F) g := by
    intro c σ
    have := int_list (μ := Bs.μSS) (expand k r (tsOf u c σ))
      (fun cw p => xiP Bs p • Rw cw.2 (rho Bs p F) g) (fun cw => Rw cw.2 (JF Bs F) g) (fun cw hcw => by
        have hw := expand_words (tsOf u c σ) cw hcw
        rw [tsOf_length] at hw
        obtain ⟨h1, h2⟩ := key cw.2 hw.1 hw.2
        exact ⟨h1, h2⟩)
    exact ⟨this.1, this.2⟩

  have hae : (fun p => xiP Bs p • rho Bs p (C3.AAop k r r le_rfl u F) g) =ᵐ[Bs.μSS]
      fun p => ∑ c, coefC c g • ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
    rw [rho_aa Bs hn.1 u hp hgG, aa_expand u _ g hgG (loc_rho Bs hn.1 hp hgG _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm, wsum, smul_list_sum]
    congr 2
    refine List.map_congr_left fun cw _ => ?_
    exact smul_comm _ _ _

  have hlocJ : Loc (r : ℕ∞) (JF Bs F) g := by
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hW.1 g ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg.2⟩
    exact ⟨U, F', hU, hgU, by exact_mod_cast hc, fun x hx hxG => he x hx (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hxG)⟩
  show ∫ p, xiP Bs p • rho Bs p (C3.AAop k r r le_rfl u F) g ∂Bs.μSS = _
  rw [integral_congr_ae hae, aa_expand u _ g hgG hlocJ]
  have hI2 : ∀ c : Fin r → Fin (2 * r + k + 1), Integrable (fun p => ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum) Bs.μSS :=
    fun c => integrable_finsetSum _ fun σ _ => (hIc c σ).1.smul ((Equiv.Perm.sign σ : ℤ) : ℂ)
  calc ∫ p, ∑ c, coefC c g • ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum ∂Bs.μSS
      = ∑ c, ∫ p, coefC c g • ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((expand k r (tsOf u c σ)).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum ∂Bs.μSS :=
        integral_finsetSum _ (fun c _ => (hI2 c).smul (coefC c g))
    _ = ∑ c, coefC c g • ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) • wsum u c σ (JF Bs F) g := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [integral_smul]
        congr 1
        refine (integral_finsetSum _ fun σ _ => ?_).trans ?_
        · exact (hIc c σ).1.smul ((Equiv.Perm.sign σ : ℤ) : ℂ)
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [integral_smul, (hIc c σ).2]

end Formalism.FourierDecayAlt.P
