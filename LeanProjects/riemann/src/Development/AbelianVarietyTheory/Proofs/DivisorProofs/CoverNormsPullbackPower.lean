import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

section Induces

open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem generatesAt_genAt_pow (D : Y.Dv) (k : ℕ) (x : Y.X) : (k • D).GeneratesAt x (genAt D x ^ k) := by
  have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn D x).nsmul k)
  rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this

theorem induces_twist_of_induced {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hA : A.Induced M L k cf) (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p)
    (hj : V.j ≫ b = V.π ≫ M.j) : V.Induces (A.twist 0 (-cf)) (L.pull b hb) k := by
  haveI := M.ar.isIntegral
  obtain ⟨-, r, hr, h₁, h₂⟩ := hA
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  set ψ := SmallSec.fnMap V.π hη with hψ
  have hφ : ∀ t, V.φ t = ψ t := fun t => by rw [e]
  have hg (x : Y.X) := generatesAt_genAt_pow A.D k x
  have hch : ∀ (i : ((L.pull b hb).B.pull V.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V.j).U i,
      V.π x ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L.B b V.j i hx) PUnit.unit
    have h2 : (V.j ≫ b) x = M.j (V.π x) := by rw [hj]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show M.j (V.π x) ∈ L.B.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull b hb).B.pull V.j).ι → V.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hmem : V.π (genericPoint V.G) ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) := ⟨hch i _ hij.1, hch j _ hij.2⟩
    have h0 : genericPoint Y.X ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) :=
      (genericPoint_specializes _).mem_open (TopologicalSpace.Opens.isOpen _) hmem
    have le : ((L.pull b hb).B.pull V.j).U i ⊓ ((L.pull b hb).B.pull V.j).U j ≤
        V.π ⁻¹ᵁ ((L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr.isRatSec _ _ h0, map_mul, ← ProjSpace.fnOf_appLE V.π hη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L.B M.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.B.pull b) V.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hj _ _ _ _ _
  · intro i x hx
    have hU := (hr.isEqn _ _ (hch i x hx)).generatesAt_iff.1 (hg (V.π x))
    rw [hr', hφ, ← map_pow, ← map_mul]
    exact unitAt_fnMap_of V.π hη hU
  · intro σ z y y' i e₁ e₂ hi
    change (Real.exp (-(2 * ((A.n : ℕ) : ℝ) * (A.ci (InfinitePlace.mk σ) + 0))) *
        C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ (k : ℕ) =
      ‖ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z‖ ^ 2 *
        Real.exp (-((L.pull b hb).φ _).φ (i PUnit.unit) y')
    let y₀ := Points.PtsOver.map b hb _ y'
    have e₂' : y₀.1 = y.1 ≫ M.j := by
      show y'.1 ≫ b = y.1 ≫ M.j
      rw [e₂, e₁, Category.assoc, hj, Category.assoc]
    have hπ₀ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hi₀ : under y ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := hπ₀ ▸ hch i _ hi
    have H := h₁ σ y y₀ (fun _ => i PUnit.unit PUnit.unit) _ e₂' hi₀ (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at H
    have hU := (hr.isEqn _ _ hi₀).generatesAt_iff.1 (hg (under y))
    have hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y₀ :=
      (L.φ _).pull_φ b hb (i PUnit.unit) y'
    have hv : ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z =
        ratVal (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) y := by
      have hU' : RegAt (V.π (under z)) (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
        rw [hπ₀]; exact hU.regAt
      rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of V.π hη hU'),
        SmallSec.ratVal_eq_valAt y hU.regAt, SmallSec.valAt_fnMap V.π hη z.1 hU', ← e₁]
    rw [hw, hv, ← H, add_zero, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  · intro v e y z yt i e₁ e₂ hi
    change ((k : ℕ) : ℝ) * (A.lg v e y - ((A.n : ℕ) : ℝ) * (-cf) v) =
      Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ (k : ℕ) * (r' i : V.G.functionField))))
    have e₂' : spMap e.O.subtype ≫ (yt ≫ b) = y.1 ≫ M.j := by
      rw [← Category.assoc, e₂, Category.assoc, hj, ← Category.assoc, e₁]
    have hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := h₂ v e y (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e₂' hi'
    have hmem : below y.1 ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hU := (hr.isEqn _ _ hmem).generatesAt_iff.1 (hg (below y.1))
    have hπ₀ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU' : RegAt (V.π (below z)) (genAt A.D (below y.1) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
      rw [hπ₀]; exact hU.regAt
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at H
    rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.valAt_fnMap V.π hη z hU', e₁, Pi.neg_apply]
    linarith [H]

end Induces

theorem norms_pull_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p), V.j ≫ b = V.π ≫ M.j → Norms V (L.pull b hb) (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => ((k : ℕ) : ℝ) * lnAdl A σ y) (fun v e y => ((k : ℕ) : ℝ) * A.lg v e y + ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * cf v) := by
  intro F _ _ C Y A M L k cf hA V b hb hj
  refine (norms_of_induces (induces_twist_of_induced hA V b hb hj)).congr (fun _ => rfl) (fun σ y => ?_) fun v e y => ?_
  · simp only [lnAdl, Adl.twist, Pi.add_apply, Pi.zero_apply, add_zero]
  · simp only [Adl.twist, Pi.neg_apply]
    ring

end GlobalTheory.CoverNorm
