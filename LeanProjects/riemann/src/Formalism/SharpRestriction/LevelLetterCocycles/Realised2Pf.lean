import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfAssemble
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfArcChoices
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfTeichOnto
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicFrobeniusPowerSeriesX

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem basis_of {I : BaseId W} {T : LocLat G Qp LL O} (hInj : I.Inj) (hFull : I.Full)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T) (i : ZMod n) :
    ∃ (r : ℕ) (e : Fin r → C.V) (b : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i)),
      ∀ k, (b k : C.V) = e k := by
  obtain ⟨r, e, hli, hsp⟩ := free_of hInj hFull hmod C i
  refine ⟨r, e, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp), fun k => ?_⟩
  simp [Module.Basis.span_apply]

theorem matrix_of {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] {N₂ : Submodule (PowerSeries O) V₂} {r₁ r₂ : ℕ} (f : V₁ → V₂)
    (e₁ : Fin r₁ → V₁) (e₂ : Fin r₂ → V₂) (b₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥N₂)
    (hb₂ : ∀ k, (b₂ k : V₂) = e₂ k) (hf : ∀ k, f (e₁ k) ∈ N₂) :
    ∃ P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O), ∀ k, ∃ a : Fin r₂ → PowerSeries O,
      f (e₁ k) = ∑ l, a l • e₂ l ∧ ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l) := by
  refine ⟨Matrix.toLin' (Matrix.of fun l k => PowerSeries.constantCoeff (b₂.repr ⟨_, hf k⟩ l)),
    fun k => ⟨fun l => b₂.repr ⟨_, hf k⟩ l, ?_, fun l => by simp⟩⟩
  have h := b₂.sum_repr ⟨_, hf k⟩
  have h' := congrArg (fun x : ↥N₂ => (x : V₂)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb₂] at h'
  exact h'.symm

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero LL]
  [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]

theorem realised2_pf (Lb : LevB W) (hR : Ring9 W) (e : W.DD W.one) (uZ : ℤ_[PD.p]ˣ)
    (ιZ : ℤ_[PD.p] →+* O)
    (hLevN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hCmp : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (hLevBφ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) • φVB PD (LL := LL) (V := T.V)
            (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (hLevBΓ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hLevΓ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ f : LetA O n, W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hLevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4Lev : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDdR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hHod : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ →
      F.Onto → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hV : ValRing O v) (hK : Function.Bijective (algebraMap K₀ K))
    (hpm : (PD.p : O) ∈ maximalIdeal O) (hrich : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (he : UnitGen W e) (hone : IsCrys PD W.one.ρ) (h5 : 5 ≤ PD.p) : Realised2 hR e := by
  intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hCu hKJ hJ hg hS hT
  obtain ⟨C₁, C₂, C₀, hC, e₀, he₀⟩ :=
    Formalism.MainNotions.N.Ln03.Pf.coordSteps_holds hR hs hP9 hLem3 hDdR he hone hK h5 T₁ T₂ F hc₁ hc₂ hon
  refine ⟨{ C₁ := C₁, C₂ := C₂, C₀ := C₀, h := hC, e₀ := e₀, Ks := KsW W, Δ := DeltaT PD.p },
    { he₀ := he₀, arcs := fun ϖ hϖ c hc => ?_ }⟩
  have hp2 : PD.p ≠ 2 := by omega
  have hp9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := fun T hT =>
    ((hP9 T hT hs hp2).2.2 (unram_of hK)).2
  obtain ⟨r₁, e₁, b₁, hb₁⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₁ hc₁.2.2.2) C₁
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨r₂, e₂, b₂, hb₂⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₂ hc₂.2.2.2) C₂
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨P, hP⟩ := matrix_of (latHomOf hC).f e₁ e₂ b₂ hb₂ (fun k =>
    (latHomOf hC).map_N _ _ (by rw [← hb₁ k]; exact (b₁ k).2))
  exact Formalism.MainNotions.N.Ln03.Pf.finalArc_holds Lb uZ ιZ hC c _ _ ϖ j _ _ Gp S η ty e₁ e₂ P hLevN hCmp hLevBφ
    hLevBΓ hLevΓ hLevφ hs hP4 hP4Lev hSat hP3 hP9 hP5 hDdR hHod hc₁ hc₂ hon hKJ hV hK hϖ hpm
    (Formalism.MainNotions.N.Ln03.Pf.hn_of hCu hc) hrich (glue2 hR) (cyclotomicFrobeniusPowerSeries_X W)
    (fun s _ ζ hζ => rhoZ_exp c ζ ⟨s + 1, (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 hζ⟩)
    huZ hutie (Formalism.MainNotions.N.Ln03.Pf.teichOnto_holds PD.p) h5 b₁ hb₁ b₂ hb₂ hP
    (Formalism.MainNotions.N.Ln03.Pf.hj_of hCu hc) (Formalism.MainNotions.N.Ln03.Pf.three_g_le_parameter_bound PD.hp.two_le hg)

end Formalism.MainNotions.N.Ln03
