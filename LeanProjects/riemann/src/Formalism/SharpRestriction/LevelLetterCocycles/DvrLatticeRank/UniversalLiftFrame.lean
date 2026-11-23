import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SatDVR
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.AevalMemOfStable
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DecompCoord

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable {W}

theorem gam_b {T : LocLat G Qp LL O} (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hIF : IsFrame W Pt π' Eπ h' M σ c α β)
    (hcr : IsCrys PD T.ρ) (hjump : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM1 : 1 ≤ M)
    {uE uE' : LetA O n} (huE'Δ : uE' ∈ W.AΔ) (huu : uE' * uE = 1) (hγE : W.γA W.gamK Eπ = uE * Eπ)
    (w : W.DD T) (hw : w ∈ InvS W T π' Eπ h' 1 c) (b₀ : LA W T π' c) (hb₀ : b₀ ∈ LamLA W T π' Eπ h' c ⊤)
    (hβ : β T ⟨w, (Submodule.mem_inf.mp hw).1⟩ = mkLA W T π' Eπ h' M c b₀ hb₀) :
    γLA W T π' c b₀ - b₀ ∈ piNL W T Pt π' Eπ h' c 1 := by
  obtain ⟨-, -, -, -, -, -, -, hβγ, -⟩ := hIF.1 T hcr hjump
  have hwL : w ∈ LamPS W T Eπ h' c := (Submodule.mem_inf.mp hw).1
  have hgw : W.γD T W.gamK w ∈ LamPS W T Eπ h' c :=
    ModelFPf.LamPS_γ (W := W) (T := T) (Eπ := Eπ) (h' := h') (c := c) huu hγE hwL
  have hgb : γLA W T π' c b₀ ∈ LamLA W T π' Eπ h' c ⊤ :=
    ModelFPf.LamLA_γ (W := W) (T := T) (π' := π') (Eπ := Eπ) (h' := h') (c := c) huE'Δ huu hγE hb₀
  have h1 := hβγ w hwL b₀ hb₀ hβ hgw hgb
  have hsub : W.γD T W.gamK w - w ∈ LamPS W T Eπ h' c := Submodule.sub_mem _ hgw hwL
  have hβs : β T ⟨W.γD T W.gamK w - w, hsub⟩ =
      mkLA W T π' Eπ h' M c (γLA W T π' c b₀ - b₀) (Submodule.sub_mem _ hgb hb₀) := by
    have e : (⟨W.γD T W.gamK w - w, hsub⟩ : ↥(LamPS W T Eπ h' c)) = ⟨_, hgw⟩ - ⟨w, hwL⟩ := rfl
    rw [e, map_sub, h1, hβ]
    rfl
  have hy : W.γD T W.gamK w - w ∈ PiNS W T π' 1 := ((mem_InvS W T π' Eπ h' 1 c w).1 hw).2
  exact (hMF.2.2.1 1 le_rfl hM1).2 _ hsub _ _ hβs hy

theorem coords_of {T : LocLat G Qp LL O} {π' Eπ : LetA O n} {h' : ℕ} {c : ZMod n} {r : ℕ}
    (bL : Basis (Fin r) O (LcQ W T π' c)) {z : LA W T π' c} (hz : z ∈ LamLA W T π' Eπ h' c ⊤) :
    ∃ g : Fin r → LetA O n, (∀ i, g i ∈ W.AΔ) ∧ ∀ i, algebraMap (LetA O n) W.EE (Eπ ^ h') *
      TensorProduct.equivFinsuppOfBasisRight bL z i = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g i) := by
  have h := (MQ.range_iff π' c bL _).1 hz
  choose g hg e using h
  refine ⟨g, hg, fun i => ?_⟩
  rw [← e i, MQ.smulLA_eq, MQ.coord_smulE]

theorem serMul_sum {V : Type} [AddCommGroup V] [Module LL V] (gp : PowerSeries LL) {ι : Type*}
    (s : Finset ι) (F : ι → ℤ → V) (m₀ : ℤ) (hF : ∀ k, ∀ t < m₀, F k t = 0) (i : ℤ) :
    serMul gp (fun t => ∑ k ∈ s, F k t) i = ∑ k ∈ s, serMul gp (F k) i := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, i - m₀ < N := ⟨(i - m₀).toNat + 1, by omega⟩
  rw [ModelFPf.serMul_eq_sum gp _ m₀ (fun t ht => Finset.sum_eq_zero fun k _ => hF k t ht) i N hN]
  rw [Finset.sum_congr rfl fun k _ => ModelFPf.serMul_eq_sum gp (F k) m₀ (hF k) i N hN]
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

theorem pt_fil {T : LocLat G Qp LL O} (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n)
    (hM5 : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c →
      ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
        f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i))
    {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (rep : Fin r → W.DD T)
    (hrep : ∀ k, rep k ∈ NcS W T (c - 1)) (hbrep : ∀ k, bL k = mkL W T π' c (rep k) (hrep k))
    (b₀ : LA W T π' c) (hb₀ : b₀ ∈ LamLA W T π' Eπ h' c ⊤) (hγb : γLA W T π' c b₀ - b₀ ∈ NL W T Pt π' Eπ h' c)
    (g : Fin r → LetA O n) (hg : ∀ i, g i ∈ W.AΔ)
    (hgeq : ∀ i, algebraMap (LetA O n) W.EE (Eπ ^ h') * TensorProduct.equivFinsuppOfBasisRight bL b₀ i =
      algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g i))
    (τ : K →ₐ[Qp] LL) (ζ : LL) (hpt : Pt c ζ τ)
    (h0 : PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0) (h1 : PowerSeries.coeff 1 (W.lev c ζ Eπ) ≠ 0) :
    ∀ t : ℤ, t ≠ 0 → Phi W T c ζ rep (fun i => ev W c ζ Eπ h' (g i) t) ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-t) := by
  intro t ht
  apply hM5 b₀ hb₀ hγb τ ζ hpt (fun t => Phi W T c ζ rep (fun i => ev W c ζ Eπ h' (g i) t)) _ t ht
  refine ⟨⟨-(h' : ℤ), fun t ht => ?_⟩, r, fun i => ⟨g i, hg i⟩, rep, ⟨hrep, ?_⟩, fun i => ?_⟩
  · dsimp only
    rw [Phi_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [ev_of_lt _ (by omega), zero_smul]
  · show smulLA W T π' c (Eπ ^ h') b₀ = _
    conv_lhs => rw [tensor_eq_sum W T π' c bL (smulLA W T π' c (Eπ ^ h') b₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MQ.smulLA_eq, MQ.coord_smulE, hgeq i, hbrep i]
  · simp only [Phi_apply]
    rw [serMul_sum _ _ _ (-(h' : ℤ)) (fun k t ht => by rw [ev_of_lt _ (by omega), zero_smul])]
    show _ = ∑ j, serC (W.lev c ζ (g j)) (valAt W T c ζ (rep j)) i
    exact Finset.sum_congr rfl fun k _ => serMul_ev h0 h1 (g k) (valAt W T c ζ (rep k)) i

set_option maxHeartbeats 1000000 in

theorem universal_lift_frame [IsDomain O] (hdvr : IsDiscreteValuationRing O) (hfr : IsFractionRing O LL)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n) (S η m : ℕ) (up : (K →ₐ[Qp] LL) → Bool)
    (b : (K →ₐ[Qp] LL) → ℕ) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hIF : IsFrame W Pt π' Eπ h' M σ c α β)
    (hcr : IsCrys PD T₂.ρ) (hjump : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hML : ModelL W T₂ Pt π' Eπ h' M c) (hM1 : 1 ≤ M)

    (hEΔ : Eπ ∈ W.AΔ) (hπΔ : π' ∈ W.AΔ)
    (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hgam : W.gamK = W.gam)
    (hγE : ∃ uE ∈ W.AΔ, ∃ uE' ∈ W.AΔ, uE' * uE = 1 ∧ W.γA W.gam Eπ = uE * Eπ)
    (hγπ : ∃ uπ ∈ W.AΔ, W.γA W.gam π' = π' * uπ)

    (τs : Finset (K →ₐ[Qp] LL)) (hτs : ∀ τ ζ, Pt c ζ τ → τ ∈ τs) (hcard : τs.card ≤ finrank K₀ K)
    (hPo : ∀ τ ζ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hb : ∀ τ, 0 < b τ) (hbS : ∀ τ, b τ + S ≤ h')

    (hlevE : ∀ τ ζ, Pt c ζ τ → PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 ∧
      PowerSeries.coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (hlevπ : ∀ τ ζ, Pt c ζ τ → PowerSeries.constantCoeff (W.lev c ζ π') ≠ 0)
    (hlevγ : ∀ τ ζ, Pt c ζ τ → ∀ a : LetA O n, W.lev c ζ (W.γA W.gam a) =
      PowerSeries.rescale (algebraMap O LL ((Formalism.MainNotions.DeltaInvariantLattices.uU W : Oˣ) : O)) (W.lev c ζ a))

    (r : ℕ) (bL : Basis (Fin r) O (LcQ W T₂ π' c)) (rep : Fin r → W.DD T₂)
    (hrep : ∀ k, rep k ∈ NcS W T₂ (c - 1)) (hbrep : ∀ k, bL k = mkL W T₂ π' c (rep k) (hrep k))
    (hvadd : ∀ τ ζ, Pt c ζ τ → ∀ x y, x ∈ NcS W T₂ (c - 1) → y ∈ NcS W T₂ (c - 1) →
      valAt W T₂ c ζ (x + y) = valAt W T₂ c ζ x + valAt W T₂ c ζ y)
    (hvsmul : ∀ τ ζ, Pt c ζ τ → ∀ (a : O) x, x ∈ NcS W T₂ (c - 1) →
      valAt W T₂ c ζ (a • x) = algebraMap O LL a • valAt W T₂ c ζ x)
    (hvpt : ∀ τ ζ ζ', Pt c ζ τ → Pt c ζ' τ → ∀ k, valAt W T₂ c ζ (rep k) = valAt W T₂ c ζ' (rep k))
    (hUPz : ∀ τ ζ, Pt c ζ τ → up τ = true → ∀ i : ℤ, i < -((b τ : ℤ) + S) → ∀ d : Fin r → LL,
      Phi W T₂ c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-i) → d = 0)
    (hUPc : ∀ τ ζ, Pt c ζ τ → up τ = true →
      r ≤ finrank LL ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (b τ)).comap (Phi W T₂ c ζ rep)) + m)
    (hDN : ∀ τ ζ, Pt c ζ τ → up τ = false →
      finrank LL ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-(b τ : ℤ) + 1)).comap (Phi W T₂ c ζ rep)) ≤ m)
    (hDNall : ∀ τ ζ, Pt c ζ τ → up τ = false → ∀ d : Fin r → LL,
      Phi W T₂ c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-((b τ : ℤ) + S))) :
    FirstPropositionFrame W F Pt π' Eπ h' M c S η m up b β := by
  classical
  haveI := hdvr
  haveI := hfr
  intro _hHyp
  obtain ⟨uE, huEΔ, uE', huE'Δ, huu, hγE'⟩ := hγE
  obtain ⟨uπ, huπΔ, hγπ'⟩ := hγπ
  have hγEK : W.γA W.gamK Eπ = uE * Eπ := by rw [hgam]; exact hγE'
  have hγπK : W.γA W.gamK π' = π' * uπ := by rw [hgam]; exact hγπ'
  obtain ⟨hNLle, hNLγ, hNLA, -, -, -, hM5⟩ := hML
  have hletΔ : (letE c : LetA O n) ∈ W.AΔ := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W c
  have hlet2 : (letE c : LetA O n) * (letE c : LetA O n) = letE c := by
    funext i; simp [letE, Pi.single_apply]

  set uO : Oˣ := Formalism.MainNotions.DeltaInvariantLattices.uU W with huO
  set u : LL := algebraMap O LL (uO : O) with hu
  have hu0 : u ≠ 0 := (uO.isUnit.map (algebraMap O LL)).ne_zero
  have hupow : ∀ t : ℤ, algebraMap O LL ((uO ^ t : Oˣ) : O) = u ^ t := by
    intro t
    have h := congrArg (fun x : LLˣ => (x : LL)) (map_zpow (Units.map (algebraMap O LL).toMonoidHom) uO t)
    rw [hu]
    rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at h
    exact h
  set PΩ : Polynomial O := ∏ i ∈ OmF W c S h' up b, (Polynomial.X - Polynomial.C ((uO ^ i : Oˣ) : O)) with hPΩ
  have hPΩ1 : Polynomial.eval 1 PΩ = piOm1 W c S h' up b := by
    rw [hPΩ, Polynomial.eval_prod]
    unfold piOm1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hPΩz : ∀ t ∈ OmF W c S h' up b, Polynomial.aeval (u ^ t) PΩ = 0 := by
    intro t ht
    rw [hPΩ, map_prod]
    apply Finset.prod_eq_zero ht
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hupow, sub_self]
  have hOmUP : ∀ τ ζ, Pt c ζ τ → up τ = true → ∀ t : ℤ, -((b τ : ℤ) + S) ≤ t → t < -(b τ : ℤ) →
      t ∈ OmF W c S h' up b := by
    intro τ ζ hpt hup t h1 h2
    unfold OmF
    rw [Finset.mem_filter, Finset.mem_Icc]
    have := hbS τ
    exact ⟨⟨by omega, by omega⟩, τ, hPo τ ζ hpt, Or.inl ⟨hup, h1, h2⟩⟩
  have hOmDN : ∀ τ ζ, Pt c ζ τ → up τ = false → ∀ t : ℤ, (b τ : ℤ) ≤ t → t < (b τ : ℤ) + S →
      t ∈ OmF W c S h' up b := by
    intro τ ζ hpt hup t h1 h2
    unfold OmF
    rw [Finset.mem_filter, Finset.mem_Icc]
    have := hbS τ
    exact ⟨⟨by omega, by omega⟩, τ, hPo τ ζ hpt, Or.inr ⟨hup, h1, h2⟩⟩

  have hPhipt : ∀ τ ζ ζ', Pt c ζ τ → Pt c ζ' τ → ∀ d, Phi W T₂ c ζ rep d = Phi W T₂ c ζ' rep d := by
    intro τ ζ ζ' h h' d
    simp only [Phi_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hvpt τ ζ ζ' h h' k]

  set UPs := τs.filter (fun τ => up τ = true ∧ ∃ ζ, Pt c ζ τ) with hUPs
  set DNs := τs.filter (fun τ => up τ = false ∧ ∃ ζ, Pt c ζ τ) with hDNs
  have hζU : ∀ τ : UPs, ∃ ζ, Pt c ζ τ := fun τ => (Finset.mem_filter.1 τ.2).2.2
  have hζD : ∀ τ : DNs, ∃ ζ, Pt c ζ τ := fun τ => (Finset.mem_filter.1 τ.2).2.2
  choose ζU hζU' using hζU
  choose ζD hζD' using hζD
  have hupU : ∀ τ : UPs, up τ = true := fun τ => (Finset.mem_filter.1 τ.2).2.1
  have hupD : ∀ τ : DNs, up τ = false := fun τ => (Finset.mem_filter.1 τ.2).2.1
  obtain ⟨k, ell, Lr, P, hrank, hCell, hrest, hPkill⟩ := decomp_coord (LL := LL) bL
    (fun τ : UPs => (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (b τ)).comap (Phi W T₂ c (ζU τ) rep))
    (fun τ => hUPc τ (ζU τ) (hζU' τ) (hupU τ))
    (fun τ : DNs => (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-(b τ : ℤ) + 1)).comap (Phi W T₂ c (ζD τ) rep))
    (fun τ => hDN τ (ζD τ) (hζD' τ) (hupD τ))

  set repE : Fin k → W.DD T₂ := fun j => ∑ i, bL.repr (ell j) i • rep i with hrepE
  have hrepE_mem : ∀ j, repE j ∈ NcS W T₂ (c - 1) := fun j =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hrep i)
  have hmkE : ∀ j, mkL W T₂ π' c (repE j) (hrepE_mem j) = ell j := by
    intro j
    calc mkL W T₂ π' c (repE j) (hrepE_mem j)
        = ∑ i, bL.repr (ell j) i • mkL W T₂ π' c (rep i) (hrep i) :=
          mkL_sum (W := W) Finset.univ _ rep hrep (hrepE_mem j)
      _ = ∑ i, bL.repr (ell j) i • bL i := by simp only [← hbrep]
      _ = ell j := bL.sum_repr _
  have hvalE : ∀ τ ζ, Pt c ζ τ → ∀ j, valAt W T₂ c ζ (repE j) =
      Phi W T₂ c ζ rep (fun i => algebraMap O LL (bL.repr (ell j) i)) := by
    intro τ ζ hpt j
    rw [Phi_apply]
    exact valAt_sum ζ (hvadd τ ζ hpt) (hvsmul τ ζ hpt) Finset.univ _ rep hrep
  have hFilE : ∀ j τ ζ, Pt c ζ τ → up τ = true →
      valAt W T₂ c ζ (repE j) ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (b τ) := by
    intro j τ ζ hpt hup
    have hτ : τ ∈ UPs := Finset.mem_filter.2 ⟨hτs τ ζ hpt, hup, ζ, hpt⟩
    rw [hvalE τ ζ hpt j, hPhipt τ ζ (ζU ⟨τ, hτ⟩) hpt (hζU' _)]
    exact hCell j ⟨τ, hτ⟩
  have hFilD : ∀ j τ ζ, Pt c ζ τ → up τ = false →
      valAt W T₂ c ζ (repE j) ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-((b τ : ℤ) + S)) := by
    intro j τ ζ hpt hup
    rw [hvalE τ ζ hpt j]
    exact hDNall τ ζ hpt hup _
  refine ⟨Lr, k, repE, hrepE_mem, ?_, ?_, ?_, ?_⟩
  ·
    have hdis : Disjoint UPs DNs := by
      rw [Finset.disjoint_left]
      intro τ h1 h2
      have a1 := (Finset.mem_filter.1 h1).2.1
      have a2 := (Finset.mem_filter.1 h2).2.1
      rw [a1] at a2
      exact Bool.noConfusion a2
    have hsub : UPs ∪ DNs ⊆ τs := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hc
    calc finrank O Lr ≤ (Fintype.card UPs + Fintype.card DNs) * m := hrank
      _ = (UPs.card + DNs.card) * m := by rw [Fintype.card_coe, Fintype.card_coe]
      _ ≤ finrank K₀ K * m := Nat.mul_le_mul_right _ (hc.trans hcard)
  · intro j τ _ hup ζ hpt
    exact hFilE j τ ζ hpt hup
  · rw [eq_top_iff, ← bL.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : ∑ j, P j i • ell j ∈ Submodule.span O (Set.range fun j => mkL W T₂ π' c (repE j) (hrepE_mem j)) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hmkE j⟩)
    have e : bL i = ∑ j, P j i • ell j + (bL i - ∑ j, P j i • ell j) := by abel
    rw [SetLike.mem_coe, e]
    exact Submodule.add_mem_sup h1 (hrest i)
  · intro w hw
    have hwL : w ∈ LamPS W T₂ Eπ h' c := (Submodule.mem_inf.mp hw).1
    obtain ⟨⟨b₀, hb₀⟩, hβ⟩ := Submodule.Quotient.mk_surjective _ (β T₂ ⟨w, hwL⟩)
    have hβ' : β T₂ ⟨w, hwL⟩ = mkLA W T₂ π' Eπ h' M c b₀ hb₀ := hβ.symm
    have hγb := gam_b Pt π' Eπ h' M σ c α β hIF hcr hjump hMF hM1 huE'Δ huu hγEK w hw b₀ hb₀ hβ'
    have hγbN : γLA W T₂ π' c b₀ - b₀ ∈ NL W T₂ Pt π' Eπ h' c := piNL_le hπΔ hNLA hγb
    obtain ⟨g, hg, hgeq⟩ := coords_of bL hb₀
    set X : Fin r → W.EE := fun i => TensorProduct.equivFinsuppOfBasisRight bL b₀ i with hX

    obtain ⟨y, hyN, hy⟩ := hγb
    obtain ⟨hh, hhΔ, hheq⟩ := coords_of bL (hNLle hyN)
    have hXγ : ∀ i, algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK (X i) - X i) =
        algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * hh i)) := by
      intro i
      have e1 : W.γE W.gamK (X i) - X i = algebraMap (LetA O n) W.EE π' *
          TensorProduct.equivFinsuppOfBasisRight bL y i := by
        rw [hX]
        dsimp only
        rw [← coord_γLA W T₂ π' c bL b₀ i, ← coord_sub W T₂ π' c bL, ← hy, pow_one, MQ.smulLA_eq,
          MQ.coord_smulE]
      rw [e1, mul_left_comm, hheq i, ← map_mul]

    set G : Fin k → LetA O n := fun j => ∑ i, algebraMap O (LetA O n) (P j i) * g i with hG
    set H : Fin k → LetA O n := fun j => ∑ i, algebraMap O (LetA O n) (P j i) * hh i with hH
    set fj : Fin k → W.EE := fun j => ∑ i, algebraMap O W.EE (P j i) * X i with hfj_def
    have hGΔ : ∀ j, G j ∈ W.AΔ := fun j =>
      Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hg i)
    have hHΔ : ∀ j, H j ∈ W.AΔ := fun j =>
      Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hhΔ i)
    have hfj : ∀ j, algebraMap (LetA O n) W.EE (Eπ ^ h') * fj j =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * G j) := by
      intro j
      simp only [hfj_def, hG, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, hgeq i, ← map_mul]
      congr 1
      ring
    have hfjγ : ∀ j, algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gam (fj j) - fj j) =
        algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * H j)) := by
      intro j
      have hγfj : W.γE W.gam (fj j) = ∑ i, algebraMap O W.EE (P j i) * W.γE W.gam (X i) := by
        simp only [hfj_def, map_sum, map_mul, AlgHom.commutes]
      rw [hγfj, hfj_def]
      dsimp only
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, hH]
      dsimp only
      rw [Finset.mul_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx := hXγ i
      rw [hgam] at hx
      rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← mul_sub, mul_left_comm, hx, ← map_mul]
      congr 1
      ring

    set f' : Fin k → W.EE := fun j => Polynomial.aeval (W.γE W.gam).toLinearMap PΩ (fj j) with hf'_def
    set a' : Fin k → LetA O n := fun j => Polynomial.aeval (twA W uE' h') PΩ ((letE c : LetA O n) * G j)
      with ha'_def
    have ha'Δ : ∀ j, a' j ∈ W.AΔ := fun j =>
      aeval_twA_mem uE' h' huE'Δ PΩ (Subalgebra.mul_mem _ hletΔ (hGΔ j))
    have ha'c : ∀ j, a' j = (letE c : LetA O n) * Polynomial.aeval (twA W uE' h') PΩ (G j) := fun j =>
      aeval_twA_letE uE' h' c PΩ (G j)
    have hf'a : ∀ j, algebraMap (LetA O n) W.EE (Eπ ^ h') * f' j = algebraMap (LetA O n) W.EE (a' j) :=
      fun j => EE_aeval Eπ h' uE uE' huu hγE' PΩ (fj j) _ (hfj j)
    have hf'γ : ∀ j, algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gam (f' j) - f' j) =
        algebraMap (LetA O n) W.EE (Polynomial.aeval (twA W uE' h') PΩ (π' * ((letE c : LetA O n) * H j))) := by
      intro j
      have e : W.γE W.gam (f' j) - f' j =
          Polynomial.aeval (W.γE W.gam).toLinearMap PΩ (W.γE W.gam (fj j) - fj j) := by
        rw [map_sub]
        exact congrArg (· - f' j) (aeval_comm (W.γE W.gam).toLinearMap PΩ (fj j)).symm
      rw [e]
      exact EE_aeval Eπ h' uE uE' huu hγE' PΩ _ _ (hfjγ j)

    set Sπ : Submodule O (LetA O n) :=
      (Subalgebra.toSubmodule W.AΔ).map (LinearMap.mulLeft O (π' * (letE c : LetA O n))) with hSπ_def
    have hSπ : ∀ v ∈ Sπ, twA W uE' h' v ∈ Sπ := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : twA W uE' h' z ∈ W.AΔ := by
        simpa using aeval_twA_mem uE' h' huE'Δ Polynomial.X hz
      refine ⟨uπ * twA W uE' h' z, Subalgebra.mul_mem _ huπΔ hz', ?_⟩
      simp only [LinearMap.mulLeft_apply, twA_apply, map_mul, hγπ', Formalism.MainNotions.LiftingTheory.gammaA_letter_idempotent]
      ring
    have hzmem : ∀ j, Polynomial.aeval (twA W uE' h') PΩ (π' * ((letE c : LetA O n) * H j)) ∈ Sπ :=
      fun j => aeval_mem_of_stable Sπ (twA W uE' h') hSπ PΩ ⟨H j, hHΔ j, by simp⟩
    choose zj hzjΔ hzj using fun j => Submodule.mem_map.1 (hzmem j)
    simp only [LinearMap.mulLeft_apply] at hzj

    have hpf : ∀ τ ζ, Pt c ζ τ → ∀ t : ℤ, t ≠ 0 →
        Phi W T₂ c ζ rep (fun i => ev W c ζ Eπ h' (g i) t) ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-t) :=
      fun τ ζ hpt => pt_fil Pt π' Eπ h' M c hM5 bL rep hrep hbrep b₀ hb₀ hγbN g hg hgeq τ ζ hpt
        (hlevE τ ζ hpt).1 (hlevE τ ζ hpt).2
    have hevG : ∀ j (ζ : LL) (t : ℤ), ev W c ζ Eπ h' (G j) t =
        ∑ i, algebraMap O LL (P j i) * ev W c ζ Eπ h' (g i) t := by
      intro j ζ t
      simp only [hG, ev_sum, ev_alg]
    have hUPv : ∀ j τ ζ, Pt c ζ τ → up τ = true → ∀ t : ℤ, t < -((b τ : ℤ) + S) →
        ev W c ζ Eπ h' (G j) t = 0 := by
      intro j τ ζ hpt hup t ht
      have hb1 := hb τ
      have hv := hUPz τ ζ hpt hup t ht _ (hpf τ ζ hpt t (by omega))
      rw [hevG]
      exact Finset.sum_eq_zero fun i _ => by
        rw [show ev W c ζ Eπ h' (g i) t = 0 from congrFun hv i, mul_zero]
    have hDNv : ∀ j τ ζ, Pt c ζ τ → up τ = false → ∀ t : ℤ, t < (b τ : ℤ) → t ≠ 0 →
        ev W c ζ Eπ h' (G j) t = 0 := by
      intro j τ ζ hpt hup t ht ht0
      have hτ : τ ∈ DNs := Finset.mem_filter.2 ⟨hτs τ ζ hpt, hup, ζ, hpt⟩
      have hv' : Phi W T₂ c (ζD ⟨τ, hτ⟩) rep (fun i => ev W c ζ Eπ h' (g i) t) ∈
          Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (-(b τ : ℤ) + 1) := by
        rw [← hPhipt τ ζ (ζD ⟨τ, hτ⟩) hpt (hζD' _)]
        exact u3upPf_FilC_anti T₂ τ (a := -t) (a' := -(b τ : ℤ) + 1) (by omega) (hpf τ ζ hpt t ht0)
      rw [hevG]
      exact hPkill ⟨τ, hτ⟩ _ hv' j
    have heva' : ∀ j τ ζ, Pt c ζ τ → ∀ t : ℤ,
        ev W c ζ Eπ h' (a' j) t = Polynomial.aeval (u ^ t) PΩ * ev W c ζ Eπ h' (G j) t := by
      intro j τ ζ hpt t
      rw [ha'c j, ev_letE]
      exact ev_aeval_twA c ζ Eπ h' (hlevE τ ζ hpt).1 (hlevE τ ζ hpt).2 uE uE' huu hγE' u hu0
        (hlevγ τ ζ hpt) PΩ (G j) t
    have hUPa : ∀ j τ ζ, Pt c ζ τ → up τ = true → ∀ t : ℤ, t < -(b τ : ℤ) → ev W c ζ Eπ h' (a' j) t = 0 := by
      intro j τ ζ hpt hup t ht
      rw [heva' j τ ζ hpt t]
      by_cases h : t < -((b τ : ℤ) + S)
      · rw [hUPv j τ ζ hpt hup t h, mul_zero]
      · rw [hPΩz t (hOmUP τ ζ hpt hup t (by omega) ht), zero_mul]
    have hDNa : ∀ j τ ζ, Pt c ζ τ → up τ = false → ∀ t : ℤ, t < (b τ : ℤ) + S → t ≠ 0 →
        ev W c ζ Eπ h' (a' j) t = 0 := by
      intro j τ ζ hpt hup t ht ht0
      rw [heva' j τ ζ hpt t]
      by_cases h : t < (b τ : ℤ)
      · rw [hDNv j τ ζ hpt hup t h ht0, mul_zero]
      · rw [hPΩz t (hOmDN τ ζ hpt hup t (by omega) ht), zero_mul]

    have h1tw : ∀ j, algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (f' j) =
        algebraMap (LetA O n) W.EE (twA W uE' h' (a' j)) := by
      intro j
      have := EE_aeval Eπ h' uE uE' huu hγE' Polynomial.X (f' j) (a' j) (hf'a j)
      simpa [Polynomial.aeval_X] using this
    have htw : ∀ j, twA W uE' h' (a' j) - a' j = π' * (letE c : LetA O n) * zj j := by
      intro j
      apply W.EE_inj
      rw [map_sub, ← h1tw j, ← hf'a j, ← mul_sub, hf'γ j, hzj j]
    have hevtw : ∀ j τ ζ, Pt c ζ τ → ∀ t : ℤ,
        ev W c ζ Eπ h' (twA W uE' h' (a' j) - a' j) t = (u ^ t - 1) * ev W c ζ Eπ h' (a' j) t := by
      intro j τ ζ hpt t
      have hsub : ∀ x y : LetA O n, ev W c ζ Eπ h' (x - y) t = ev W c ζ Eπ h' x t - ev W c ζ Eπ h' y t := by
        intro x y
        have := ev_add (W := W) (c := c) (ζ := ζ) (Eπ := Eπ) (h' := h') (x - y) y t
        rw [sub_add_cancel] at this
        rw [this, add_sub_cancel_right]
      have htw1 := ev_aeval_twA c ζ Eπ h' (hlevE τ ζ hpt).1 (hlevE τ ζ hpt).2 uE uE' huu hγE' u hu0
        (hlevγ τ ζ hpt) Polynomial.X (a' j) t
      rw [Polynomial.aeval_X, Polynomial.aeval_X] at htw1
      rw [hsub, htw1]
      ring
    have hzlev : ∀ j τ ζ, Pt c ζ τ → ∀ t₀ : ℤ, (∀ t < t₀, (u ^ t - 1) * ev W c ζ Eπ h' (a' j) t = 0) →
        ∀ m₁ : ℕ, (m₁ : ℤ) < t₀ + h' → PowerSeries.coeff m₁ (W.lev c ζ (zj j)) = 0 := by
      intro j τ ζ hpt t₀ ht m₁ hm₁
      refine ps_coeff_cancel (W.lev c ζ π') (W.lev c ζ (zj j)) (hlevπ τ ζ hpt) (m₁ + 1) (fun i hi => ?_) m₁
        (Nat.lt_succ_self _)
      have h1 := lev_zero_of_ev (hlevE τ ζ hpt).2 (twA W uE' h' (a' j) - a' j) t₀
        (fun t htt => by rw [hevtw j τ ζ hpt t]; exact ht t htt) i (by omega)
      rwa [htw j, _root_.map_mul (W.lev c ζ), _root_.map_mul (W.lev c ζ), ModelFPf.lev_letE, mul_one] at h1
    have hzUP : ∀ j τ ζ, Pt c ζ τ → up τ = true → ∀ m₁ : ℕ, (m₁ : ℤ) < h' - b τ →
        PowerSeries.coeff m₁ (W.lev c ζ (zj j)) = 0 := by
      intro j τ ζ hpt hup m₁ hm₁
      exact hzlev j τ ζ hpt (-(b τ : ℤ)) (fun t ht => by rw [hUPa j τ ζ hpt hup t ht, mul_zero]) m₁ (by omega)
    have hzDN : ∀ j τ ζ, Pt c ζ τ → up τ = false → ∀ m₁ : ℕ, (m₁ : ℤ) < h' + b τ + S →
        PowerSeries.coeff m₁ (W.lev c ζ (zj j)) = 0 := by
      intro j τ ζ hpt hup m₁ hm₁
      refine hzlev j τ ζ hpt ((b τ : ℤ) + S) (fun t ht => ?_) m₁ (by omega)
      by_cases h0 : t = 0
      · rw [h0, zpow_zero, sub_self, zero_mul]
      · rw [hDNa j τ ζ hpt hup t ht h0, mul_zero]

    have hcoord : ∀ j, IsCoord W Pt π' Eπ h' S up b c (f' j) := by
      intro j
      refine ⟨a' j, ha'Δ j, ?_, hf'a j, ?_, ?_, letE c * zj j, Subalgebra.mul_mem _ hletΔ (hzjΔ j), ?_⟩
      · rw [ha'c j, ← mul_assoc, hlet2]
      · intro τ ζ hpt hup i hi
        exact lev_zero_of_ev (hlevE τ ζ hpt).2 (a' j) (-(b τ : ℤ)) (hUPa j τ ζ hpt hup) i (by omega)
      · intro τ ζ hpt hup
        exact ⟨ev W c ζ Eπ h' (a' j) 0, fun i hi => lev_const_of_ev (hlevE τ ζ hpt).1 (hlevE τ ζ hpt).2 (a' j)
          ((b τ : ℤ) + S) (hDNa j τ ζ hpt hup) i (by omega)⟩
      · rw [hgam, hf'γ j, ← hzj j, mul_assoc]

    have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
    have hiv : ∀ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j) ∈ InvL W T₂ Pt π' Eπ h' c ⊤ := by
      intro j
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · show smulLA W T₂ π' c (Eπ ^ h') (f' j ⊗ₜ _) ∈ LinearMap.range (toLA W T₂ π' c ⊤)
        rw [ModelFPf.smulLA_tmul, hf'a j, ha'c j]
        have := ModelFPf.rep_mem (W := W) (T := T₂) (π' := π') (c := c)
          (fun _ : Fin 1 => Polynomial.aeval (twA W uE' h') PΩ (G j))
          (fun _ => aeval_twA_mem uE' h' huE'Δ PΩ (hGΔ j)) (fun _ => repE j) (fun _ => hrepE_mem j)
        rwa [Fin.sum_univ_one] at this
      · set Gc : W.EE := ((hΛu.unit⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * zj j)
          with hGc_def
        have hΛGc : algebraMap (LetA O n) W.EE (Eπ ^ h') * Gc =
            algebraMap (LetA O n) W.EE ((letE c : LetA O n) * zj j) := by
          rw [hGc_def, ← mul_assoc, hΛu.mul_val_inv, one_mul]
        have hGc : W.γE W.gamK (f' j) - f' j = algebraMap (LetA O n) W.EE π' * Gc := by
          have e1 : algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK (f' j) - f' j) =
              algebraMap (LetA O n) W.EE (Eπ ^ h') * (algebraMap (LetA O n) W.EE π' * Gc) := by
            rw [hgam, hf'γ j, ← hzj j, mul_left_comm, hΛGc, ← map_mul, mul_assoc]
          exact (hΛu.mul_right_inj).1 e1
        rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, ModelFPf.γLA_tmul,
          ← TensorProduct.sub_tmul, hGc]
        refine ⟨Gc ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j), Submodule.subset_span ?_, ?_⟩
        · refine ⟨1, fun _ => ⟨zj j, hzjΔ j⟩, fun _ => repE j, ⟨fun _ => hrepE_mem j, ?_⟩, ?_⟩
          · rw [Fin.sum_univ_one]
            show smulLA W T₂ π' c (Eπ ^ h') (Gc ⊗ₜ _) = _
            rw [ModelFPf.smulLA_tmul, hΛGc]
          · intro τ ζ hpt i
            show (∑ _ : Fin 1, serC (W.lev c ζ (zj j)) (valAt W T₂ c ζ (repE j)) i) ∈ _
            rw [Fin.sum_univ_one]
            unfold serC
            split_ifs with hi
            · by_cases hup : up τ = true
              · by_cases hlow : i < (h' : ℤ) - b τ
                · rw [hzUP j τ ζ hpt hup _ (by omega), zero_smul]
                  exact Submodule.zero_mem _
                · exact Submodule.smul_mem _ _ (u3upPf_FilC_anti T₂ τ (a := b τ) (a' := h' - i) (by omega)
                    (hFilE j τ ζ hpt hup))
              · have hup' : up τ = false := by simpa using hup
                by_cases hlow : i < (h' : ℤ) + b τ + S
                · rw [hzDN j τ ζ hpt hup' _ (by omega), zero_smul]
                  exact Submodule.zero_mem _
                · exact Submodule.smul_mem _ _ (u3upPf_FilC_anti T₂ τ (a := -((b τ : ℤ) + S)) (a' := h' - i)
                    (by omega) (hFilD j τ ζ hpt hup'))
            · exact Submodule.zero_mem _
        · rw [pow_one, ModelFPf.smulLA_tmul]

    set ρ : Fin r → LcQ W T₂ π' c := fun i => bL i - ∑ j, P j i • ell j with hρ
    set xr : LA W T₂ π' c := ∑ i, Polynomial.aeval (W.γE W.gam).toLinearMap PΩ (X i) ⊗ₜ ρ i with hxr
    have hb0 : b₀ = ∑ i, X i ⊗ₜ bL i := tensor_eq_sum W T₂ π' c bL b₀
    have hb₀dec : b₀ = ∑ i, X i ⊗ₜ ρ i + ∑ j, fj j ⊗ₜ ell j := by
      have e : ∀ i, X i ⊗ₜ[O] bL i = X i ⊗ₜ ρ i + ∑ j, (algebraMap O W.EE (P j i) * X i) ⊗ₜ ell j := by
        intro i
        rw [show bL i = ρ i + ∑ j, P j i • ell j by simp [hρ], TensorProduct.tmul_add, TensorProduct.tmul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
      rw [hb0, Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← TensorProduct.sum_tmul]
    have hstar : Polynomial.aeval (γLA W T₂ π' c) PΩ b₀ =
        xr + ∑ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j) := by
      conv_lhs => rw [hb₀dec]
      rw [map_add, map_sum, map_sum]
      simp only [aeval_γLA_tmul, hgam, hmkE]
      rfl
    have hxrL : xr ∈ LamLA W T₂ π' Eπ h' c Lr := by
      show smulLA W T₂ π' c (Eπ ^ h') xr ∈ LinearMap.range (toLA W T₂ π' c Lr)
      rw [hxr, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [ModelFPf.smulLA_tmul, EE_aeval Eπ h' uE uE' huu hγE' PΩ (X i) _ (hgeq i), aeval_twA_letE]
      exact ⟨⟨Polynomial.aeval (twA W uE' h') PΩ (g i), aeval_twA_mem uE' h' huE'Δ PΩ (hg i)⟩ ⊗ₜ
        ⟨ρ i, hrest i⟩, rfl⟩
    have hpiγ : ∀ v ∈ piNL W T₂ Pt π' Eπ h' c 1, γLA W T₂ π' c v ∈ piNL W T₂ Pt π' Eπ h' c 1 :=
      fun v hv => piNL_γ hNLγ hNLA huπΔ hγπK hv
    have hγb1 : γLA W T₂ π' c b₀ - b₀ ∈ piNL W T₂ Pt π' Eπ h' c 1 := ⟨y, hyN, hy⟩
    have hPb : γLA W T₂ π' c (Polynomial.aeval (γLA W T₂ π' c) PΩ b₀) - Polynomial.aeval (γLA W T₂ π' c) PΩ b₀ ∈
        piNL W T₂ Pt π' Eπ h' c 1 := by
      rw [← aeval_comm, ← map_sub]
      exact aeval_mem_of_stable _ _ hpiγ PΩ hγb1
    have hxrI : xr ∈ InvL W T₂ Pt π' Eπ h' c Lr := by
      refine Submodule.mem_inf.2 ⟨hxrL, ?_⟩
      rw [Submodule.mem_comap]
      have e : xr = Polynomial.aeval (γLA W T₂ π' c) PΩ b₀ -
          ∑ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j) := by
        rw [hstar, add_sub_cancel_right]
      rw [LinearMap.sub_apply, LinearMap.id_apply, e]
      have e3 : γLA W T₂ π' c (Polynomial.aeval (γLA W T₂ π' c) PΩ b₀ -
            ∑ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j)) -
          (Polynomial.aeval (γLA W T₂ π' c) PΩ b₀ - ∑ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j)) =
          (γLA W T₂ π' c (Polynomial.aeval (γLA W T₂ π' c) PΩ b₀) - Polynomial.aeval (γLA W T₂ π' c) PΩ b₀) -
            ∑ j, (γLA W T₂ π' c (f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j)) -
              f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j)) := by
        rw [map_sub, map_sum, Finset.sum_sub_distrib]
        abel
      rw [e3]
      refine Submodule.sub_mem _ hPb (Submodule.sum_mem _ fun j _ => ?_)
      have h4 := Submodule.mem_comap.1 (Submodule.mem_inf.1 (hiv j)).2
      rwa [LinearMap.sub_apply, LinearMap.id_apply] at h4
    have hx : piOm1 W c S h' up b • b₀ ∈ LamLA W T₂ π' Eπ h' c ⊤ := Submodule.smul_mem _ _ hb₀
    refine ⟨f', piOm1 W c S h' up b • b₀, hx, xr, hcoord, hiv, hxrI, ?_, ?_⟩
    · have e : (⟨piOm1 W c S h' up b • w, (LamPS W T₂ Eπ h' c).smul_mem _ (Submodule.mem_inf.mp hw).1⟩ :
          ↥(LamPS W T₂ Eπ h' c)) = piOm1 W c S h' up b • ⟨w, hwL⟩ := rfl
      rw [e, map_smul, hβ']
      rfl
    · have hroot : (PΩ - Polynomial.C (Polynomial.eval 1 PΩ)).IsRoot 1 := by simp
      obtain ⟨R, hR⟩ : ∃ R, PΩ - Polynomial.C (Polynomial.eval 1 PΩ) = R * (Polynomial.X - Polynomial.C 1) :=
        ⟨_, by rw [mul_comm]; exact (Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot).symm⟩
      have h3 : Polynomial.aeval (γLA W T₂ π' c) (PΩ - Polynomial.C (Polynomial.eval 1 PΩ)) b₀ =
          Polynomial.aeval (γLA W T₂ π' c) R (γLA W T₂ π' c b₀ - b₀) := by
        rw [hR, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
          LinearMap.sub_apply, Module.End.one_apply]
      have e2 : piOm1 W c S h' up b • b₀ - ∑ j, f' j ⊗ₜ mkL W T₂ π' c (repE j) (hrepE_mem j) - xr =
          -(Polynomial.aeval (γLA W T₂ π' c) R (γLA W T₂ π' c b₀ - b₀)) := by
        rw [← h3, map_sub, LinearMap.sub_apply, Polynomial.aeval_C, Module.algebraMap_end_apply, hPΩ1, hstar]
        abel
      rw [e2]
      exact Submodule.neg_mem _ (aeval_mem_of_stable _ _ hpiγ R hγb1)

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
