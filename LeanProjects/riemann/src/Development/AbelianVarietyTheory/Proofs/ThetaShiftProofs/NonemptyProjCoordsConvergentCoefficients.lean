import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisFSum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffMemSubfield
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNoCommonZero

noncomputable section

namespace GlobalTheory.SpanFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts GlobalTheory.AmpleSpan
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem top_le_of_mem {K : Type} [Field K] {Z : Scheme.{0}} (x : Sp K ⟶ Z) {V : Z.Opens} (p : Sp K) (h : x p ∈ V) :
    ⊤ ≤ x ⁻¹ᵁ V := fun q _ => by
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact h

theorem exists_lift {Z Y : Scheme.{0}} (x : Y ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ x' : Y ⟶ V.toScheme, x' ≫ V.ι = x :=
  ⟨IsOpenImmersion.lift V.ι x (by rintro _ ⟨p, rfl⟩; exact ⟨⟨x p, h trivial⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_coords_of_basis (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}}
    [IsLocallyNoetherian S] {s : S ⟶ Sp B} (o : Obj D l bb s) {A : AnArc (𝓞 E)} {y : Sp ℂ⸨X⸩ ⟶ S}
    (Φ : GenPts A o.t y) (hA : AnFin A) (hΦ : Φ.Rational) (N : ℕ) [NeZero N] (hN : 4 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    (hrat : ∀ f : A.V → ℂ⸨X⸩, IsComb A N Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
      ∃ T : ℝ, IsComb A N (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T) : Nonempty (Coords Φ N) := by
  have hLB : o.t.PP.L.IsLB := o.t.PP.isLB
  have := o.proper
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hy := top_le_of_mem y _ hyU
  have : IsAffine U := hU
  obtain ⟨m, b, hb⟩ := exists_span_powOver hL.secBaseChange (objPolAV o) (N := N) (by omega) hU
  have emb : EmbedsBy (o.t.G.hom ∣_ U) b :=
    embedsBy_powOver o.t.G (hL.ample S (objPolAV o) N hN).2 hU b
      (hb _ _ (𝟙 _) _ (𝟙 _) IsPullback.of_id_fst (Fin N) (fun _ => 1) _ (Category.id_comp _) (by simp) b
        fun i => (secScal_iff_sval hLB).2 fun Z r z J _ => by rw [Category.comp_id])
  obtain ⟨g, hg⟩ := exists_lift y hy
  obtain ⟨h, e, sq⟩ := exists_isPullback_restrict o.t.G (φ := pullback.fst o.t.G.hom y)
    (f' := pullback.snd o.t.G.hom y) (g := g) (by rw [hg]; exact IsPullback.of_hasPullback _ _)
  choose b' hb' _ using fun i => existsUnique_secScal hLB (φ := fun _ : Fin N => (o.t.G.hom ⁻¹ᵁ U).ι)
    (ε := fun _ => 1) (h := h) (formEq_const (K' := Fin 1) (ε' := fun _ => (N : ℤ)) e (by simp)) (b i)
  have span := hb _ _ h _ g sq (Fin 1) (fun _ => (N : ℤ)) _ e (by simp) b' hb'
  choose f hf hf' using fun i => Φ.span N (b' i)
  have hfib : ∀ v, fib (Φ.x v) ≫ pullback.fst o.t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  have val : ∀ i v (x' : Sp ℂ⸨X⸩ ⟶ (o.t.G.hom ⁻¹ᵁ U).toScheme) (j : o.t.PP.L.ι),
      x' ≫ (o.t.G.hom ⁻¹ᵁ U).ι = (Φ.x v).left → ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR x' ((Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f i v * Φ.τ v j ^ N :=
    fun i v x' j hx hj => by
      obtain rfl : x' = fib (Φ.x v) ≫ h := by
        rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ U).ι, Category.assoc, e, hfib, hx]
      rw [← hfib] at hj
      exact (valR_of_secScal e (hb' i) _ j hj).trans (hf' i v j hj)
  have chart : ∀ v, ∃ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart hLB ((Φ.x v).left (default : PrimeSpectrum ℂ⸨X⸩))
    exact ⟨j, top_le_of_mem _ _ hj⟩
  have conv : ∀ i v, f i v ∈ Conv.convLaurent := fun i v => by
    obtain ⟨x₀, hx₀⟩ := hΦ.1 v
    obtain ⟨j, hj⟩ := chart v
    have down : ∀ V, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ V → ⊤ ≤ x₀ ⁻¹ᵁ V := fun V hV => by
      rw [← hx₀] at hV
      exact top_le_of_mem x₀ _ (hV (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial)
    obtain ⟨x₁, rfl⟩ := exists_lift x₀ (down (o.t.G.hom ⁻¹ᵁ U) (by
      have w : (Φ.x v).left ≫ o.t.G.hom = y := Over.w (Φ.x v)
      rw [← Scheme.Hom.comp_preimage, w]
      exact hy))
    have h1 := val i v _ j ((Category.assoc _ _ _).trans hx₀) hj
    have hx₁ : ⊤ ≤ x₁ ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j) :=
      fun p _ => Set.mem_iInter.2 fun _ => down _ hj (x := p) trivial
    replace h1 := (HolHom.valR_spMap _ x₁ _ hx₁ _).symm.trans h1
    have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
    rw [← div_eq_iff h2] at h1
    rw [← h1]
    exact div_mem (Subtype.prop _) (pow_mem (hΦ.2 v j hj) _)
  obtain ⟨T, hm, hc, hz⟩ := exists_no_common_zero hA (by omega) hth hli hsp f (fun i => hrat _ (hf i) (conv i))
    fun β t ht => by
      obtain ⟨c, hc⟩ := span (Φ.sig N β t)
      refine ⟨fun i => valR (𝟙 _) ⊤ (c i), fun v => ?_⟩
      obtain ⟨j, hj⟩ := chart v
      have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
      rw [← hfib] at hj
      have hw : ⊤ ≤ fib (Φ.x v) ⁻¹ᵁ LB.wchart o.t.PP.L (fun _ : Fin 1 => pullback.fst o.t.G.hom y) (fun _ => j) :=
        fun z hz => Set.mem_iInter.2 fun _ => hj hz
      refine mul_right_cancel₀ h2 ((Φ.val N β t ht v j hj).symm.trans ?_)
      refine (congrArg (valR (fib (Φ.x v)) _) (hc fun _ => j)).trans ((HolHom.valR_eq _ _ hw _).trans ?_)
      rw [Finset.sum_mul]
      refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)
      rw [_root_.mul_assoc, ← hf' i v j hj]
      refine congrArg₂ (· * ·) ?_ (HolHom.valR_eq _ _ hw _).symm
      refine (HolHom.valR_eq _ _ hw _).symm.trans ((HolHom.valR_appLE _ _ ⊤ _ le_top _ hw).trans ?_)
      rw [fib, pullback.lift_snd]
  exact ⟨⟨T, U, hU, hy, m, b, emb, fun i v => ⟨f i v, hm i v⟩, hc, val, hz⟩⟩

theorem nonempty_coords : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) , AnFin A → Φ.Rational → ∀ (N : ℕ) [NeZero N], 4 ≤ N → Nonempty (Coords Φ N) := by
  intro hL _ E _ _ _ H _ D l B _ bb S _ s o A y Φ hA hΦ N _ hN
  obtain ⟨n, α, th, -, hth, hli, -, hsp⟩ := AnArc.exists_basis_FSum _ A hA N
  exact nonempty_coords_of_basis hL o Φ hA hΦ N hN hth hli hsp (exists_isComb_halfRing _ A hA N)

end GlobalTheory.SpanFrame
