import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotientStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.CardH0TwistedDual
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.BkPair
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk.Eul

theorem chi_tie (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧
      PadicInt.toZModPow n u = (Formalism.GaloisCohomology.cycK l K.1 n (K.1.fixingSubgroupEquiv g) : ZMod (l ^ n)) := by
  have hcyc : GlobalTheory.Cyc.IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) =
      ((D.loc l).χQ (K.1.fixingSubgroupEquiv.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Cyc.TwistLift.isCyc_unique hcyc (GlobalTheory.Cyc.isCyc_cycChar l)]; rfl
  refine ⟨(χZ (K.1.fixingSubgroupEquiv g) : ℤ_[l]), ?_, rfl⟩
  have h1 := hχZ (K.1.fixingSubgroupEquiv g)
  rw [show K.1.fixingSubgroupEquiv.symm (K.1.fixingSubgroupEquiv g) = g from K.1.fixingSubgroupEquiv.symm_apply_apply g, ← (D.loc l).PD_χ K g] at h1
  exact h1

section Act

variable {G : Type} [Group G] {Qp LL O V : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (m : ↥L.T ⧸ I) : actQ L I hI 1 m = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 x) = _
  congr 1
  apply Subtype.ext
  change ρ 1 (x : V) = x
  simp

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (g h : G) (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) x) = Submodule.Quotient.mk (actT L g (actT L h x))
  congr 1
  apply Subtype.ext
  change ρ (g * h) (x : V) = ρ g (ρ h x)
  simp [Module.End.mul_apply]

end Act

theorem psi_unit {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (ι : ℤ_[l] →+* O) (J : Ideal O)
    (n : ℕ) (hN : ((l ^ n : ℕ) : O) ∈ J) (ψ : (O ⧸ J) →+ ZMod (l ^ n)) (u : ℤ_[l]) (p : O) :
    ψ (Ideal.Quotient.mk J (ι u * p)) = PadicInt.toZModPow n u * ψ (Ideal.Quotient.mk J p) := by
  have hl : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set m : ℕ := (PadicInt.toZModPow n u : ZMod (l ^ n)).val with hm
  have hmc : ((m : ℕ) : ZMod (l ^ n)) = PadicInt.toZModPow n u := ZMod.natCast_zmod_val _
  have hk : u - (m : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hmc, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hk
  have hu : u = (m : ℤ_[l]) + v * (l : ℤ_[l]) ^ n := by rw [hv]; ring
  have h2 : Ideal.Quotient.mk J (ι u * p) = m • Ideal.Quotient.mk J p := by
    rw [← map_nsmul, Ideal.Quotient.eq]
    have : ι u * p - m • p = (ι v * p) * ((l ^ n : ℕ) : O) := by
      rw [hu]
      simp only [map_add, map_mul, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow]
      ring
    rw [this]
    exact J.mul_mem_left _ hN
  rw [h2, map_nsmul, nsmul_eq_mul, hmc]

theorem equivariant_B (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (ι : ℤ_[l] →+* O)
    (hι : ∀ a, algebraMap O LL (ι a) = algebraMap ℚ_[l] LL a) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hd : IsDualLat1 ((D.loc l).PD K) LA LA' P) (J : Ideal O) (I : Submodule O ↥LA.T)
    (I' : Submodule O ↥LA'.T) (hI : StableSub LA I) (hI' : StableSub LA' I')
    (B : (↥LA.T ⧸ I) →ₗ[O] (↥LA'.T ⧸ I') →ₗ[O] (O ⧸ J))
    (hB : ∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p →
      B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p)
    (g : ↥(GK K)) (x : ↥LA.T ⧸ I) (y : ↥LA'.T ⧸ I') (u : ℤ_[l])
    (hu : (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) :
    B (actQ LA I hI g x) (actQ LA' I' hI' g y) = Ideal.Quotient.mk _ (ι u) * B x y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective I x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I' y
  obtain ⟨p, hp⟩ := (hd.2 y).1 y.2 x x.2
  have h1 : P (actT LA g x) (actT LA' g y) = algebraMap O LL (ι u * p) := by
    change P (A.ρ g x) (A'.ρ g y) = _
    rw [hd.1.1 g x y, hp, map_mul, hι, hu]
    rfl
  rw [hB x y p hp, ← map_mul]
  exact hB _ _ _ h1

theorem exists_pair {O W W' : Type} [CommRing O] [AddCommGroup W] [Module O W] [AddCommGroup W']
    [Module O W'] (J : Ideal O) (N : ℕ) (B : W →ₗ[O] W' →ₗ[O] (O ⧸ J)) (ψ₀ : (O ⧸ J) →+ ZMod N)
    (hψ : ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBr : ∀ y, (∀ x, B x y = 0) → y = 0) :
    ∃ Pb : W →+ W' →+ ZMod N, (∀ x y, Pb x y = ψ₀ (B x y)) ∧ (∀ x, (∀ y, Pb x y = 0) → x = 0) ∧
      ∀ y, (∀ x, Pb x y = 0) → y = 0 := by
  have hsm : ∀ (o : O) (b : O ⧸ J), Ideal.Quotient.mk J o * b = o • b := fun o b => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    rfl
  refine ⟨AddMonoidHom.mk' (fun x => ψ₀.comp (B x).toAddMonoidHom) (fun x y => by
    ext z
    simp), fun _ _ => rfl, fun x hx => hBl x fun y => hψ _ fun o => ?_,
    fun y hy => hBr y fun x => hψ _ fun o => ?_⟩
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← map_smul]
    exact hx _
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← LinearMap.smul_apply, ← map_smul]
    exact hy _

theorem quot_killed {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (J : Ideal O) (N : ℕ)
    (hN : (N : O) ∈ J) (m : M ⧸ (J • ⊤ : Submodule O M)) : N • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul O]
  exact Submodule.smul_mem_smul hN trivial

theorem final_count (h1 w z h0 h0' q a d : ℕ) (hw : 0 < w) (hq : w = q ^ a)
    (hC : h1 * w = z * h0) (hZ : z = h0' * w ^ (d + 1)) : h1 = h0 * h0' * q ^ (a * d) := by
  apply Nat.eq_of_mul_eq_mul_right hw
  rw [hC, hZ, pow_succ, pow_mul, ← hq]
  ring

set_option maxHeartbeats 4000000 in

theorem euler_quot : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V * finrank ℚ_[l] ↥K.1) := by
  intro hT hE D l _ K LL _ _ _ O _ _ hO A A' LA LA' P hd ϖ hϖ r hI hI'
  obtain ⟨-, hqf, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨ι, hι⟩ := GlobalTheory.TateTop.exists_ringHom hO
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := id hO
  have := hdom
  have := hdvr
  have := hfr
  have := hqf
  have hfinO : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    have := Ideal.finite_quotient_pow (I := Ideal.span {ϖ}) ⟨{ϖ}, by simp⟩ r
    rwa [Ideal.span_singleton_pow] at this
  have hpos : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hN : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r} := by
    have h1 : (l : O) ^ r ∈ Ideal.span {ϖ ^ r} := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_mem_pow hl r
    rw [Nat.cast_pow, pow_succ]
    exact Ideal.mul_mem_right _ _ h1
  obtain ⟨hW, hcW⟩ := cardQ l K LL O hO A LA ϖ hϖ r
  obtain ⟨hW', -⟩ := cardQ l K LL O hO A' LA' ϖ hϖ r
  obtain ⟨ψ₀, hψ, -⟩ := GlobalTheory.T.exists_perfect_character_quotient O ϖ hϖ r (l ^ (r + 1)) hpos hfinO hN
  obtain ⟨B, hB, hBl, hBr⟩ := pairO D l K LL O hO A A' LA LA' P hd ϖ hϖ r
  obtain ⟨Pb, hPb, hL, hR⟩ := exists_pair _ _ B ψ₀ hψ hBl hBr
  have hlc := locconst D l K LL O hO A LA ϖ hϖ r hI
  have heq : ∀ g x y, Pb ((actQ LA _ hI g).toAddMonoidHom x) ((actQ LA' _ hI' g).toAddMonoidHom y) =
      (Formalism.GaloisCohomology.cycK l K.1 (r + 1) (K.1.fixingSubgroupEquiv g) : ZMod (l ^ (r + 1))) * Pb x y := by
    intro g x y
    obtain ⟨u, hu, hu'⟩ := chi_tie D l K (r + 1) g
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B x y)
    have e1 := equivariant_B D l K LL O ι hι A A' LA LA' P hd _ _ _ hI hI' B hB g x y u hu
    rw [← hb, ← map_mul] at e1
    have e3 := psi_unit ι _ (r + 1) hN ψ₀ u b
    rw [hu', hb, ← hPb, ← e1, ← hPb] at e3
    exact e3
  have hZ := cocycles hT hE l K (r + 1) (Nat.succ_pos r) _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI) (fun g h m => actQ_mul' LA _ hI g h m)
    hlc (quot_killed _ _ hN) _
    (fun g => (actQ LA' _ hI' g).toAddMonoidHom) (actQ_one' LA' _ hI') (fun g h m => actQ_mul' LA' _ hI' g h m)
    Pb hL hR heq
  have hC := h1count l K LL O A LA _ hI hW hlc
  exact final_count _ _ _ _ _ _ _ _ Nat.card_pos hcW hC hZ

end PositivityTheory.LocalTateOrthogonality.Bk.Eul
