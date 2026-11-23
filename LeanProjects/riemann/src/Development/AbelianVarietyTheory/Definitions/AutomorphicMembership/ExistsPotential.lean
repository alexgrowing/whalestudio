import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralDetOfPreservesLattice

noncomputable section

namespace GlobalTheory.Mem.ColsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_potential {G A X : Type} [Group G] [CommGroup A] (χ : G →* A) (r : G → X → X → Prop)
    (h1 : ∀ x, r 1 x x) (hi : ∀ g x y, r g x y → r g⁻¹ y x)
    (hm : ∀ g g' x y z, r g x y → r g' y z → r (g' * g) x z) (hs : ∀ g x, r g x x → χ g = 1) :
    ∃ φ : X → A, ∀ g x y, r g x y → (φ x)⁻¹ * φ y = χ g := by
  let s : Setoid X := ⟨fun x y => ∃ g, r g x y, fun x => ⟨1, h1 x⟩, fun ⟨g, h⟩ => ⟨_, hi _ _ _ h⟩,
    fun ⟨g, h⟩ ⟨g', h'⟩ => ⟨_, hm _ _ _ _ _ h h'⟩⟩
  have hb : ∀ x, ∃ g, r g (Quotient.mk s x).out x := fun x => Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun g x y h => ?_⟩
  have e : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, h⟩
  have h2 := hm _ _ _ _ _ (hm _ _ _ _ _ (hc x) h) (hi _ _ _ (hc y))
  rw [← e] at h2
  have h3 := hs _ _ h2
  simp only [map_mul, map_inv] at h3
  rw [inv_mul_eq_one] at h3
  show (χ (c x))⁻¹ * χ (c y) = χ g
  rw [h3, mul_comm (χ g), inv_mul_cancel_left]

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice L hfg hsp γ hγ

section Host

variable {R : Ranks} (H : Host R)

def chi : letI := H.cmStar; unitary H.E →* ℂˣ :=
  letI := H.cmStar
  ∏ τ : Tau R, ((Units.map (H.emb ((τ : R.Psi) : R.GG) : H.E →* ℂ)).comp
    Unitary.toUnits)⁻¹

theorem chi_apply : letI := H.cmStar; ∀ z : unitary H.E, ((chi H z : ℂˣ) : ℂ) =
    ∏ τ : Tau R, (H.emb ((τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  intro z
  simp [chi]

private theorem prod_sigmaOf (x : H.E) :
    ∏ τ : Tau R, H.sigmaOf ((τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.galois
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  have hm : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ => ⟨_, hm σ⟩) ⟨fun a b h => ?_, fun τ => ?_⟩ _ _ (fun σ => ?_)
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val h))
  · have h1 : H.sigmaOf τ H.sqd = H.sqd := (H.galE_mem_Psi_iff _).1 (by simpa [Host.sigmaOf] using τ.2)
    have h2 : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h1
      | algebraMap y => exact AlgEquiv.commutes _ y
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | inv y _ hy => rw [map_inv₀, hy]
      | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    refine ⟨IntermediateField.fixingSubgroupEquiv H.K ⟨_, h2⟩, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply _
  · simp [Host.sigmaOf]

theorem chi_of_integral : letI := H.cmStar; ∀ z : unitary H.E, IsIntegral ℤ (z : H.E) → chi H z = 1 := by
  letI := H.cmStar
  intro z hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star (z : H.E) * z = 1 := z.2.1
    have h2 : φ (star (z : H.E)) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  apply Units.ext
  rw [chi_apply]
  have h := congrArg H.φ₀ (prod_sigmaOf H (z : H.E))
  rw [H.der.norm_mu z ⟨n, hn, hp⟩, map_one, map_one, map_prod] at h
  rw [Finset.prod_inv_distrib, Units.val_one, inv_eq_one]
  exact h

theorem exists_pot (N : ℕ) : letI := H.cmStar; ∃ φ : SDLat H.E N → ℂˣ,
    ∀ (γ : Matrix.unitaryGroup (Fin N) H.E) (L L' : SDLat H.E N),
      L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      (φ L)⁻¹ * φ L' = chi H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  letI := H.cmStar
  let dt : Matrix.unitaryGroup (Fin N) H.E →* unitary H.E :=
    { toFun := fun γ => ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hone : ∀ L : Submodule (𝓞 H.E) (Fin N → H.E), SDLat.smulLat (1 : Matrix (Fin N) (Fin N) H.E) L = L := by
    intro L
    ext v
    simp [SDLat.smulLat]
  have hmul : ∀ (a b : Matrix (Fin N) (Fin N) H.E) (L : Submodule (𝓞 H.E) (Fin N → H.E)),
      SDLat.smulLat (a * b) L = SDLat.smulLat a (SDLat.smulLat b L) := by
    intro a b L
    unfold SDLat.smulLat
    rw [← Submodule.map_comp, Matrix.toLin'_mul]
    rfl
  refine exists_potential ((chi H).comp dt)
    (fun γ (L L' : SDLat H.E N) => L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1)
    (fun L => (hone _).symm) (fun γ L L' h => ?_) (fun γ γ' L L' L'' h h' => ?_) (fun γ L h => ?_)
  · rw [h, ← hmul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact (hone _).symm
  · rw [h', h, ← hmul]; rfl
  · refine chi_of_integral H _ (isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)
    rw [h]
    exact ⟨v, hv, rfl⟩

end Host

section Chain

open GlobalTheory.MemberTorsor

variable (B : Pre)

def uI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

theorem norm_uI_zpow (a b : ℤ) : ‖((uI ^ a * uI ^ b : ℂˣ) : ℂ)‖ = 1 := by
  simp [uI]

open Classical in

@[reducible] def ch (u : B.Word) : ColumnChain B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { chain B.R (Tau B.R) (B.hcW u) (B.T u) with
    rhoDet := fun i _ => ((uI⁻¹ * uI ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rhoDet' := fun i _ => ((uI * uI ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rho_norm := fun _ _ _ => by simp [uI]
    rho'_norm := fun _ _ _ => by simp [uI] }

open Classical in

@[reducible] def member (u : B.Word) : Member B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { C := ch B u
    A := { atT B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) with
      duStar := B.duStar u, duStar_pos := B.duStar_pos u, Dstar := B.Dstar, Dstar_pos := B.Dstar_pos,
      GamP := B.GamP, one_lt_gammaP := B.one_lt_gammaP }
    P := { period B.R (Tau B.R) (B.hcW u) (B.T u) with } }

@[reducible] def cols0 : Cols0 B where
  mem := member B
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).L0
  clsLat_lat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).standardTuple_isLattice
  Tup := Fin 3
  mu0 := 0
  muStar := 1
  muStar' := 2
  chTw u _ := ch B u
  memberColumns_twistedChain_base _ := rfl
  e0Tw _ _ := LinearEquiv.refl ℂ _
  PTw u _ := (member B u).P
  Dt := ℂˣ
  detCls _ _ _ := uI
  muTil _ := MonoidHom.id _
  chiD := MonoidHom.id _
  UO := ⊥
  chiD_UO x hx := Subgroup.mem_bot.1 hx
  e1Dt := chi B.host
  rest_detCharacter_on_unitary_eq := chi_apply B.host
  relDet N L L' := QuotientGroup.mk (((exists_pot B.host N).choose L)⁻¹ * (exists_pot B.host N).choose L')
  relDet_self N L := by simp
  relDet_mul N L L' L'' := by
    rw [← QuotientGroup.mk_mul, mul_assoc, mul_inv_cancel_left]
  relDet_smul N L L' γ h := by rw [(exists_pot B.host N).choose_spec γ L L' h]
  rhoDet_eq_inv_muTilde_chiD_pow _ _ _ := rfl
  rhoDetPrime_eq_muTilde_mul_chi_pow _ _ _ := rfl

open Classical in

def cols (B : Base) : Cols B where
  toCols0 := cols0 B.toPre
  fm u :=
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    { forms B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) B.LL B.embLL B.places with }

theorem two_lt_alt (u : B.Word) : 2 < B.T u := by
  have h := B.level_mod_four _ (B.T_level u)
  have h2 := (B.T_prime u).two_le
  omega

open Classical in

theorem exists_cols (B : Base) : ∃ C : Cols B, (∀ u i, Nonempty ((C.mem u).C.cls i)) ∧
    (∀ u, (C.mem u).A.Mram ≠ ⊥) ∧ (∀ u i, (C.fm u).Fi i ≠ ⊥) ∧ C.mu0 ≠ C.muStar ∧ C.mu0 ≠ C.muStar' ∧
    C.muStar ≠ C.muStar' ∧ Function.Injective C.chiD ∧ ∀ u i c, C.chiD (C.detCls u i c) ≠ 1 := by
  refine ⟨cols B, fun u i => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩, fun u => ?_, fun u i => ?_,
    (by decide : (0 : Fin 3) ≠ 1), (by decide : (0 : Fin 3) ≠ 2), (by decide : (1 : Fin 3) ≠ 2),
    fun _ _ h => h, fun u i c h => ?_⟩
  · haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    exact mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (two_lt_alt B.toPre u)
  · exact (top_ne_bot : (⊤ : Submodule ℂ ((Tau B.R → (ZMod (B.T u))ˣ) → Unit → ℂ)) ≠ ⊥)
  · have h' : uI = 1 := h
    have := congrArg (fun x : ℂˣ => (x : ℂ).re) h'
    simp [uI] at this

theorem nonempty_cols0 (B : Pre) : Nonempty (Cols0 B) := ⟨cols0 B⟩

theorem T_win (C : Cols0 B) (u : B.Word) : (C.mem u).A.Tstar ≤ ((C.mem u).A.T : ℝ) ∧
    ((C.mem u).A.T : ℝ) ≤ (1 + 1 / ((B.R.f : ℝ) * B.R.k)) * (C.mem u).A.Tstar := by
  unfold ColumnsAtT.Tstar ColumnsAtT.Xu
  rw [C.A_T, C.A_duStar, C.A_Dstar, C.A_GamP]
  exact B.T_win u

end Chain

end GlobalTheory.Mem.ColsModel

end
