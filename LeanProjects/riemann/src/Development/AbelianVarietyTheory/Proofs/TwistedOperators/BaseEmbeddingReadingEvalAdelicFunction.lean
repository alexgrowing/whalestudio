import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransformIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftSubTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionThirdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev Formalism.L2.NTheta
open GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Comm

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem levChi_datWp (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h]
  simp [LevCh.datWp, datY]

theorem model_inv_cl (hHW : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (z : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), ∀ h, (R.HW i σ).e z v (h * k) = (R.HW i σ).e z v h := by
  intro k hk h
  have hz : (R.HW i σ).e z ∈ R.Wall i σ := (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z
  rw [((GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ _ _ _ _).1 hz).lev v k hk h, levChi_datWp, one_mul]

theorem heckeOn_actW_cl {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hd : IsHkData R i P k α Rc) (g : G) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc (actW R i σ g ((R.HW i σ).e z)) = actW R i σ g (heckeOn (R.MW i σ) Rc ((R.HW i σ).e z)) := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hoF := GlobalTheory.HeckeModel.offAt_of_place (L := flagL (R.datWp i R.triv)) hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := exists_local_isDC hoL.splits hαL hR
  have key : ∀ (w : (R.HW i σ).H) v, heckeLin (Wc D i) Rc ((R.HW i σ).e w v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e w v) :=
    fun w v => funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (model_inv_cl hHW i σ w v) h
  have hg : actW R i σ g ((R.HW i σ).e z) = (R.HW i σ).e (R.gW i σ g z) := (hgW i σ g z).symm
  ext v : 1
  show heckeLin (Wc D i) Rc (actW R i σ g ((R.HW i σ).e z) v) =
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (heckeLin (Wc D i) Rc ((R.HW i σ).e z v))
  rw [hg, key, key, ← hg]
  exact (GlobalTheory.HeckeModel.heckeLin_actL hoF hαL hA₀ (fun k hk => model_inv_cl hHW i σ z v k hk.1) (R.eG g)).symm

theorem comm_rho_cl {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hd : IsHkData R i P k α Rc)
    (hinj : Function.Injective ((R.FW i).j σ))
    (hρ : RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ) {c : ℂ}
    {hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hH : HeckeJ.IsHkJ σ ((R.FW i).j σ) (R.HW i σ).e (heckeOn (R.MW i σ) Rc) c hL) (g : G) :
    hL ∘ₗ (R.FW i).ρ g = (R.FW i).ρ g ∘ₗ hL := by
  refine LinearMap.ext fun x => hinj ((hHW i σ).1 ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hH, hρ, hρ, hH, map_smul, map_smul,
    heckeOn_actW_cl hβ' hSb hHW hgW σ hd, smul_comm]

end Comm

section Prime

theorem exists_prime_under {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p f : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ Nat.card (𝓞 E ⧸ P.asIdeal) = p ^ f := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨f, hp, hf⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  refine ⟨_, f, hp, ?_, by rw [Nat.card_eq_fintype_card, hf]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem split_of_ne {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem valuation_natCast_pow {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {p : ℕ}
    (hp : (p : 𝓞 K) ∉ la.asIdeal) (f : ℕ) : la.valuation K ((p ^ f : ℕ) : K) = 1 := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K p) = 1 := by
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hp ?_)
    exact (la.valuation_lt_one_iff_mem _).1 h
  rw [map_natCast] at h1
  rw [Nat.cast_pow, map_pow, h1, one_pow]

end Prime

section Sup

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiW_eq (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R ((i : ℕ) + 1)) : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV a f = phiC T hV a f := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W), castDict hV (T.phiJ ((i : ℕ) + 1) σ a f) = phiC T hV a f := by
    intro W hV
    subst hV
    rfl
  exact key _ hV

variable {T R κ v₀}

theorem baseEmbedding_reading_eval_adelicFunction (fw : FWTie T R κ v₀) {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i)
    (hex : JEvAt T R κ v₀ i (sg0 D A) hV) (f : Cu T κ i) :
    evAt R i _ (v₀ i _) (fw.jK i (sg0 D A) f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) := by
  obtain ⟨jK, hjK⟩ := hex
  obtain ⟨j', hj'⟩ := exists_ext_of_isKsForm (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) jK
  exact fw.ev i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV
    ⟨j', fun f => (congrArg (evAt R i _ (v₀ i _)) (hj' f)).trans (hjK f)⟩ f

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem not_dvd_level (hL : LawsJ T) {P : Formalism.L2.DIV.Pl D.host.E} {p : ℕ} (hpP : (p : 𝓞 D.host.E) ∈ P.asIdeal)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : ¬ p ∣ T.Q.l.M' := by
  intro h
  have e : T.Q.l.M' = D.host.g 0 * D.host.g 1 := by
    show Nat.lcm T.Q.l.M T.Q.l.A = _
    rw [hL.pins.2.1.1, hL.pins.2.1.2, Nat.lcm_one_right]
  obtain ⟨u, hu⟩ := e ▸ h
  apply hP
  rw [hu, Nat.cast_mul]
  exact P.asIdeal.mul_mem_right _ hpP

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem exists_transform (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) (hL : LawsJ T)
    (i : Fin D.R.m) {P : Ideal (𝓞 D.host.E)} {p k : ℕ} (hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T.Q.l P p) (hk : k ≤ D.R.r)
    (cq : T.Q.c.F) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : Dom a n) :
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n, ∃ g ∈ T.cuspA ((i : ℕ) + 1) a n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P p k (hkScal T.Q.c cq P k n) f g := by
  have hpq : (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q = D.R.r := by
    have h1 := hL.pins.2.2.2 _ (inR i)
    rw [h1.1, h1.2.1]
    have := D.R.m_add_three_le_k
    have := i.2
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hE := hT.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P p k cq a n (hpq ▸ hr1) hSO (hpq ▸ hk) ha.2
  have hD : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.Detects (T.Q.Xo ((i : ℕ) + 1)) T.Q.c a n := hP.2.2.2 _ _ _ _ _ _ _ _
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P p k :=
    hP.1 _ _ _ _ _ _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨hSO.max, hSO.split, hSO.prime, hSO.under, hSO.off⟩)
  exact (GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.keepsCusp_iff_exists hE hD hF).1
    (hT.2 D T.toCore hL.toLawsM _ (inR i) P p k cq _ _ hSO hk ha)

theorem apply_eq_of_read_cl (hHW : R.models_HW) (fw : FWTie T R κ v₀) {i : Fin D.R.m}
    (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i) (hex : JEvAt T R κ v₀ i (sg0 D A) hV)
    (hinj : Function.Injective ((R.FW i).j (sg0 D A))) {Rc : Finset (GA D (Wc D i))} {c : ℂ}
    {hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hH : HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) c hL)
    {f g : Cu T κ i} (hfg : ∀ h, phiC T hV (wtA (κ i)) (g : T.R ((i : ℕ) + 1)) h =
      c * ∑ a ∈ Rc, phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * a)) :
    hL (fw.e i f : (R.FW i).WK) = (fw.e i g : (R.FW i).WK) := by
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  refine hinj (hEI ?_)
  refine Eq.trans ?_ (baseEmbedding_reading_eval_adelicFunction fw hV hex g).symm
  funext h
  rw [hfg h, ← baseEmbedding_reading_eval_adelicFunction fw hV hex f]
  unfold evAt
  rw [hH]
  rfl

theorem hkC_eq (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * (Nat.card (kP P) : ℂ)⁻¹ ^ (k * D.R.nV / 2) = hkC R i P k := by
  have e2 : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)
  rw [e2, inv_pow, inv_pow]
  rfl

variable (T R κ) in

def ReadsCusp (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g →
      ∀ h, phiC T hV (wtA (κ i)) g h = hkC R i P k * ∑ a ∈ Rc, phiC T hV (wtA (κ i)) f (h * a)

theorem readsCusp_of_readsAt {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ} {hV : T.V ((i : ℕ) + 1) σ = Wc D i}
    (hR : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt T R i σ hV (κ i)) : ReadsCusp T R κ i σ hV := by
  intro P p k α Rc _ hs f hf g hg hfg
  have hread := hR.modulus hs hf.1 hg.1 hfg
  simp only [phiW_eq, hkC_eq] at hread
  exact hread

theorem hkSupAt_of_readsCusp (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (fw : FWTie T R κ v₀)
    (hex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV)
    (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ)
    (hR : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, ReadsCusp T R κ i _ hV) :
    HkSupAt T R i := by
  intro P k α Rc hd hL hH hW la hla
  refine keeps_of _ la hL hW ?_ (comm_rho_cl hβ hSb hHW hgW _ hd hinj hρ hH)
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, hq⟩ := exists_prime_under P
  have hoff := not_dvd_level fw.laws hpP hd.2.1
  have hsp := split_of_ne (H := T.Q.H) hd.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  intro x hx
  obtain ⟨f, rfl⟩ := (fw.e i).surjective x
  obtain ⟨g, hg, hfg⟩ := exists_transform hT hP fw.laws i ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hd.2.2.1
    ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
  rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
    hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
  have hread := hR hV P p k α Rc hd ⟨hd.1, hp, hpP, hoff, hd.2.2⟩ f f.2 g hg hfg
  have heq : (⟨hL (fw.e i f), hW _ (fw.e i f).2⟩ : (R.FW i).WK) = fw.e i ⟨g, hg⟩ :=
    Subtype.ext (apply_eq_of_read_cl hHW fw hV (hex hV) hinj hH (f := f) (g := ⟨g, hg⟩) hread)
  rw [heq]
  intro y
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  refine transform_integral (hI _ _ _ _ _ _).2.2 (fw.laws.evalWD _ (inR i)) ⟨P.isMaximal, hsp, hp, hpP, hoff⟩
    (hP.1 _ _ _ _ _ _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hp, hpP, hoff⟩))
    (hla p hp hpP) ?_ f.2.1 hg.1 hfg (fun v hv => ?_) _ (fw.pt i la y).2
  · have e1 : Ideal.absNorm P.asIdeal = p ^ m := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq]
    have e2 : Nat.card (kP P) = p ^ m := hq
    rw [hkScal, e1, e2, map_mul, map_pow, map_inv₀, valuation_natCast_pow (hla p hp hpP)]
    simp
  · have := hx ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Equiv.apply_symm_apply, Core.nrmM_le_one_iff] at this
    exact this

end Sup

section Pin

abbrev withConst (T : CoreJ D) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D := { T with cE := c' }

variable (T : CoreJ D) [iA : Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def FrameOnCusp (i : Fin D.R.m) : Prop :=
  ∃ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ,
    (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ)) ∧
    (∀ (i' : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), ∀ f ∈ T.cuspA ((i' : ℕ) + 1) (wtA (κ i')) (κ i').n,
      (withConst T c').phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f = T.phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f) ∧
    ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin (withConst T c') R i T.σ₀ hV

variable {T R κ v₀}

omit iA in
theorem phiC_withConst {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {f : T.R j} (h : (withConst T c').phiJ j σ a f = T.phiJ j σ a f) :
    phiC (withConst T c') hV a f = phiC T hV a f := by
  subst hV
  exact h

set_option maxHeartbeats 1600000 in

def tieWithConst (fw : FWTie T R κ v₀) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
    (h1 : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ))
    (h2 : ∀ (i' : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), ∀ f ∈ T.cuspA ((i' : ℕ) + 1) (wtA (κ i')) (κ i').n,
      (withConst T c').phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f = T.phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f) :
    @FWTie D G _ _ Pl0 T0 A (withConst T c') iA R κ v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (withConst T c') iA R κ v₀ fw.alg_eq fw.e fw.ks fw.kap fw.pt fw.nrm_eq
    ⟨fw.laws.toLawsM, h1, fw.laws.muVal, fw.laws.muConj, fw.laws.intAll, fw.laws.modelW, fw.laws.familyUniformisationBasePointOrthogonal, fw.laws.kfHalf,
      fw.laws.adPin⟩
    fw.chiR fw.hv₀ fw.x0
    (fun i σ hσ hV h => fw.ev0 i σ hσ hV fun ⟨j', hj'⟩ => h ⟨j', fun f => (hj' f).trans (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2)).symm⟩)
    (fun i σ hσ hV h f =>
      (fw.ev i σ hσ hV (h.imp fun _ hj' f => (hj' f).trans (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2))) f).trans
        (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2)).symm)

omit iA in
theorem phiC_congr {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

omit iA in
theorem phiC_apply {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j)
    (h : GA D W) : phiC T hV a f h = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) h := by
  subst hV
  rfl

omit iA in

theorem exists_withConst (hL : LawsJ T) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c0 : (T.U j σ).Comp → ℂ) (h0 : CUnit c0) :
    ∃ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, c' j σ = c0 ∧ LawsJ (withConst T c') := by
  classical
  let Φ : ∀ p : ℕ × (T.Q.c.F →+* ℂ), (T.U p.1 p.2).Comp → ℂ := Function.update (fun p => T.cE p.1 p.2) (j, σ) c0
  have h1 : ∀ p : ℕ × (T.Q.c.F →+* ℂ), InR D p.1 → GoodEmb T.Q.c p.2 → CUnit (Φ p) := fun p h h' => by
    by_cases e : p = (j, σ)
    · subst e
      simpa only [Φ, Function.update_self] using h0
    · simpa only [Φ, Function.update_of_ne e] using hL.cUnit _ h _ h'
  exact ⟨fun j σ => Φ (j, σ), Function.update_self _ _ _,
    hL.toLawsM, fun j hj σ hσ => h1 (j, σ) hj hσ, hL.muVal, hL.muConj, hL.intAll, hL.modelW, hL.familyUniformisationBasePointOrthogonal, hL.kfHalf, hL.adPin⟩

theorem readsCusp_of_shift {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) {σ : T.Q.c.F →+* ℂ} {hV : T.V ((i : ℕ) + 1) σ = Wc D i}
    (hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f)
    {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ}
    (hR : @ReadsCusp D G _ _ Pl0 T0 A (withConst T c') iA R κ i σ hV) {z : G} {c : ℂ} (hc : c ≠ 0) (hz : ∃ k, LiftW R i z k)
    (hs : ∀ k, LiftW R i z k → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ h,
      phiC (withConst T c') hV (wtA (κ i)) f h = c * phiC T hV (wtA (κ i)) f (h * k)) : ReadsCusp T R κ i σ hV := by
  intro P p k α Rc hd hset f hf g hg hfg h
  obtain ⟨kz, hkz, e⟩ := exists_liftW_act R i hz
  obtain ⟨y, hy⟩ := hev f hf
  have h1 := hR P p k α Rc hd hset f hf g hg hfg (h * kz⁻¹)
  have h2 : ∑ a ∈ Rc, Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) ((R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)))
      (h * kz⁻¹ * a) = Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z)
        (fun x => ∑ a ∈ Rc, (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) (x * a)) (h * kz⁻¹) :=
    congrFun (congrArg (fun U : MMap (R.MW i (sg0 D A)) => U (v₀ i (sg0 D A)))
      (heckeOn_actW_cl hβ hSb hHW hgW (sg0 D A) hd z y)) (h * kz⁻¹)
  simp only [e, hy, inv_mul_cancel_right] at h2
  rw [hs kz hkz g hg, inv_mul_cancel_right, Finset.sum_congr rfl fun a _ => hs kz hkz f hf _, ← Finset.mul_sum, h2,
    mul_left_comm] at h1
  exact mul_left_cancel₀ hc h1

set_option maxHeartbeats 1600000 in

theorem readsCusp_of_clauses {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hinf : R.models_inf) (hHW : R.models_HW) (hgW : R.models_gW) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (fw : FWTie T R κ v₀) (hV₁ : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i)
    (hex : JEvAt T R κ v₀ i (sg0 D A) hV₁) (hpin₀ : ConstPinned T R κ v₀ i) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0)
    (hom : ∀ O : OMDat T.toCore R i Unit (fun _ => A.μ0),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
      ∃ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧
          GlobalTheory.AdTh.SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1)
    (hR : ∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, LawsJ (withConst T c') →
      ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV →
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV (κ i)) :
    ReadsCusp T R κ i (res T (sg0 D A)) hV₁ := by
  have hσ : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  obtain ⟨O, ph, -, hpins, hrow⟩ := hpin₀
  obtain ⟨cc, hcc, u, hu, hE0, hS⟩ := hom O hpins
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  have hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f := fun f hf =>
    ⟨_, (baseEmbedding_reading_eval_adelicFunction fw hV₁ hex ⟨f, hf⟩).trans (phiC_congr hσ hV₁ hV _ _)⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hphi : ∀ f h, phiC T hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f h :=
    fun f h => phiC_apply hV _ f h
  obtain ⟨z, c, hc, hz, hs⟩ := shift_of_span O hpins hn hHV hjV hmem hsp hrow hE0 hS fun f hf => by
    obtain ⟨y, hy⟩ := hev f hf
    exact ⟨_, (hHW i _).2.1.le (LinearMap.mem_range_self _ y), fun h => (congrFun hy h).trans (hphi f h)⟩
  obtain ⟨c', hc', hL'⟩ := exists_withConst fw.laws ((i : ℕ) + 1) T.σ₀ cc hcc.1
  have hx0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) :=
    hσ ▸ fw.x0 i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hpin := @GlobalTheory.FrameConst.framePin_of_ccIs D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV rfl hL' hinf hpins.lift.std hx0
    (by subst hc'; exact hcc)
  have hphi' : ∀ f h, phiC (withConst T c') hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.phi cc f h := fun f h => by
    subst hc'
    exact phiC_apply (T := withConst T c') hV _ f h
  have key : ReadsCusp T R κ i T.σ₀ hV := by
    refine readsCusp_of_shift (v₀ := v₀) hβ hSb hHW hgW hev
      (@readsCusp_of_readsAt D G _ _ Pl0 T0 A (withConst T c') iA R κ i _ hV (hR c' hL' hV hpin))
      (div_ne_zero hc hu0) hz fun k hk f hf h => ?_
    have h1 := hs k hk f hf h
    have h2 : O.phi (u • cc) f h = u * O.phi cc f h := by
      rw [phi_apply, phi_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hphi', hphi]
    field_simp
    rw [h2] at h1
    linear_combination (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * h1
  have gen : ∀ (σ : T.Q.c.F →+* ℂ) (hW : T.V ((i : ℕ) + 1) σ = Wc D i), σ = T.σ₀ → ReadsCusp T R κ i σ hW := by
    rintro _ _ rfl
    exact key
  exact gen _ hV₁ hσ

theorem hkSupAt_of_clauses (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hinf : R.models_inf) (hHW : R.models_HW) (hgW : R.models_gW) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (fw : FWTie T R κ v₀) (h0 : ReadAt0 T R κ v₀ i) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0)
    (hom : ∀ O : OMDat T.toCore R i Unit (fun _ => A.μ0),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
      ∃ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧
          GlobalTheory.AdTh.SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1)
    (hR : ∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, LawsJ (withConst T c') →
      ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV →
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV (κ i)) :
    HkSupAt T R i :=
  hkSupAt_of_readsCusp hI hT hP hβ hSb hHW hgW fw h0.ex h0.inj h0.rho fun hV =>
    readsCusp_of_clauses hβ hSb hinf hHW hgW hHV hjV hmem fw hV (h0.ex hV) h0.const hsp hom hR

end Pin

def HkSupFrame : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), R.Char F →
    ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
      (_fw : FWTie T R κ v₀) (i : Fin D.R.m),
      (∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV) →
      Function.Injective ((R.FW i).j (sg0 D A)) →
      RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ →
      FrameOnCusp T R κ i → HkSupAt T R i

end GlobalTheory.HeckeSup
