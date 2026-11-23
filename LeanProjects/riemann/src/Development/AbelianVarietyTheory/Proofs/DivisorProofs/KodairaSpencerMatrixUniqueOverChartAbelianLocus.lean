import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartKSUniq

theorem isKS_unique_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ n v hv hb D Θ Θ' h h'
  haveI : CharZero (ChartRing k m d) :=
    charZero_of_injective_algebraMap (R := k) (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d)))
  let φ : Γ(Sp (ChartRing k m d), ⊤) →+* FractionRing (ChartRing k m d) :=
    (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).commRingCatIsoToRingEquiv.injective
  have hx : spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) = jK (ChartRing k m d) := by
    show spMap φ ≫ (isAffineOpen_top (Sp (ChartRing k m d))).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp [φ]
  set R := ChartRing k m d with hRdef
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) :=
    GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have hf : (∏ i, bdParam k m d i : R) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ h0 => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this
  have hV : ⊤ ≤ (spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ
      (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, bdParam k m d i)) := by
    intro p _
    change (spMap φ) p ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen _
    rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen]
    show PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen _
    rw [PrimeSpectrum.mem_basicOpen]
    show _ ∉ Ideal.comap φ p.asIdeal
    haveI := p.isPrime
    rw [Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal, Ideal.mem_bot]
    intro h0
    apply hf
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero, ← h0]
    show _ = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _))
    rw [Iso.inv_hom_id_apply]
  have key := GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint E H (Sp R) t _ (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) n v hv hb
    (FractionRing R) φ P.A _ hV (by rw [hx]; exact gpG) hL _ Θ Θ' h h'
  ext a b
  exact hφ (congrFun₂ key a b)

end GlobalTheory.ChartKSUniq
