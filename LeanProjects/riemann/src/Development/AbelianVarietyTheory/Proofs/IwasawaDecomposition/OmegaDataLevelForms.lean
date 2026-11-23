import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCuspIsThClsDUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastPosWtAOfPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMUMatMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmulEntry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowZeroMulRightIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitCOfCXiAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedClassSum

open GlobalTheory.GeoLevel GlobalTheory.Member Formalism.L2.Host

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem natCast_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) :
    (l.M : 𝓞 E) ∈ l.Mb :=
  Ideal.mul_le_left (l.prod.ge (Ideal.mem_span_singleton_self _))

set_option maxHeartbeats 1000000 in

theorem exists_root_value (l : Level H) {V : HSp D} {k : GA D V} (hk : k ∈ GfC V) {c : (AE D)ˣ →* Circle}
    {χ : HChar D.host.E} (hc : ChrEq c χ) (ht : ∀ P, χ.TameAt P) (Q : Finset (Pl D.host.E))
    (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ) (hres : ∀ P ∈ Q, IsRes χ P (ch P)) (hQ : ∀ P ∈ Q, l.Mb ≤ P.asIdeal)
    (hram : ∀ P, ¬ χ.UnrAt P → P ∈ Q ∨ ∃ P' ∈ Q, Lev.IsConjPl P' P) (U : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hU : unswap D U = (finHom V k).1.det) (u : ∀ P : Q, (kP P.1)ˣ) (hu : ∀ P : Q, (u P : kP P.1) = resS D.host.F P.1 U) :
    ∃ x, IsDetRoot V k x ∧ ((c x : Circle) : ℂ) = ∏ P : Q, ((ch P.1 (u P) : ℂˣ) : ℂ) := by
  have hM0 : l.Mb ≠ ⊥ := fun e => by
    have h1 := natCast_mem_Mb l
    have h2 := l.three_le
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    omega
  obtain ⟨a, b, s, s', hb, hs, hs', hin, hout⟩ := exists_half_elements l (Ideal.finite_factors hM0).toFinset fun P => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le] at hin hout
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hyp⟩ := exists_root_half l.M U a b s s' hb hs hs'
    (by rw [hU]; exact GlobalTheory.RecDict.det_finHom_norm V k)
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hx : FinUnit x := ⟨hx1, hx2 ▸ hy, hx3 ▸ hy'⟩
  refine ⟨x, isDetRoot_of_fin hk hx1 (by rw [hx2, ← hU]; exact hroot), ?_⟩
  let p' : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨Lev.swapAE D p, swap_int hp⟩
  refine char_finUnit hc ht Q ch hres hx (oToS _ _ a + oToS _ _ b * U + oToS _ _ l.M * p') ?_ _ (fun P => ?_) fun P hP => ?_
  · rw [hx2, hyp, ← unswap_swap p]
    exact map_coe_sum _ (unswap D) _ _ U _ p' l.M (map_natCast _ l.M)
  · exact (hu P).trans (resS_sum_left P.1 U p' hs (hin P.1 (hQ _ P.2)).2 (hin P.1 (hQ _ P.2)).1).symm
  · by_cases hun : χ.UnrAt P
    · exact Or.inl hun
    obtain ⟨P', hP', hcj⟩ := (hram P hun).resolve_left hP
    have hbar : ∀ t ∈ l.Mb, H.bar t ∈ P.asIdeal := fun t ht => by
      obtain ⟨t', h1, h2⟩ := hcj t (hQ P' hP' ht)
      rwa [show H.bar t = t' from RingOfIntegers.ext ((H.bar_eq t).trans h2.symm)]
    have hm : (l.M : 𝓞 D.host.E) ∈ P.asIdeal := by simpa using hbar _ (natCast_mem_Mb l)
    refine Or.inr (resS_sum_right P U p' hs hm (hout P (fun hle => P.isPrime.ne_top ?_) hm))
    rw [eq_top_iff, ← l.coprime]
    exact sup_le hle (Ideal.map_le_iff_le_comap.2 hbar)

theorem exists_int_matrix {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {u : GA D V} (hu : gLat V u = latHat V) :
    ∃ y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), frGL β y = Lev.finE V u ∧
      unswap D (y.1.det : Formalism.L2.Herm.intAf D.host.F D.host.E) = (finHom V u).1.det := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ : Lev.finE V u ∈ St β := by
    rw [GlobalTheory.LatStab.mem_St_iff]
    refine (GlobalTheory.LatStab.image_eq_iff (Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective
      (Formalism.L2.Herm.intAf D.host.F D.host.E) β _ (finHom V u) rfl _ fun z => ?_).1 hu
    rw [SetLike.mem_coe, hl]
    refine ⟨fun hz => (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz), fun hz => ?_⟩
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ ((hfr _).2 hz)
    convert this using 1
    funext i
    exact (unswap_swap (z i)).symm
  refine ⟨y, hy, ?_⟩
  have h2 : Lev.swapAE D (finHom V u).1.det = (Lev.finE V u).1.det := (Lev.swapAE D).map_det _
  rw [← det_frGL β y, hy, ← h2, unswap_swap]

theorem exists_of_mem_closure {A B k : Type} [CommRing A] [CommRing B] [CommRing k] (O : Subring B) (f : B →+* A) (r : O →+* k)
    (S : Set A) (h : ∀ z ∈ S, ∃ Z : O, f Z = z ∧ r Z = 0) {z : A} (hz : z ∈ AddSubgroup.closure S) :
    ∃ Z : O, f Z = z ∧ r Z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz => exact h z hz
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, h1, h2⟩ := hx
    obtain ⟨Y, h3, h4⟩ := hy
    exact ⟨X + Y, by rw [Subring.coe_add, map_add, h1, h3], by rw [map_add, h2, h4, add_zero]⟩
  | neg x _ hx =>
    obtain ⟨X, h1, h2⟩ := hx
    exact ⟨-X, by rw [Subring.coe_neg, map_neg, h1], by rw [map_neg, h2, neg_zero]⟩

set_option maxHeartbeats 1000000 in

theorem resS_eq_zero {I : Ideal (𝓞 D.host.E)} {P : Pl D.host.E} (hP : I ≤ P.asIdeal)
    {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 D.host.F (algebraMap (𝓞 D.host.E) D.host.E '' (I : Set (𝓞 D.host.E)))) :
    ∃ Z : Formalism.L2.Herm.intAf D.host.F D.host.E, unswap D Z = z ∧ resS D.host.F P Z = 0 := by
  refine exists_of_mem_closure _ (unswap D) (resS D.host.F P) _ ?_ hz
  rintro _ ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  have hm : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  refine ⟨oToS _ _ x * ⟨_, hm⟩, ?_, ?_⟩
  · rw [Subring.coe_mul, map_mul]
    change ((1 : Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) * (a ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (hP hx), zero_mul]

set_option maxHeartbeats 1000000 in

theorem exists_psi (V : HSp D) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V io) (hrk : Dw.p + Dw.q = V.rank)
    (hpq : 1 ≤ Dw.p + Dw.q) (hd : d.IsLev) (Q : Finset (Pl D.host.E)) (hQ : ∀ P ∈ Q, d.I ≤ P.asIdeal)
    (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ) (hmem : ∀ P ∈ Q, ∀ x, ((ch P x : ℂˣ) : ℂ) ∈ c.F) :
    ∃ ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ, ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d)
      (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (u : GA D V) (U : Formalism.L2.Herm.intAf D.host.F D.host.E),
      (∀ a, (Submodule.Quotient.mk (s a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
      (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
        (finHom V u).1.mulVec (finVec V (io a)) - finVec V (io (s a)) = d.l₂.M • w) →
      unswap D U = (finHom V u).1.det → ∀ v : ∀ P : Q, (kP P.1)ˣ, (∀ P : Q, (v P : kP P.1) = resS D.host.F P.1 U) →
      (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P : Q, ((ch P.1 (v P) : ℂˣ) : ℂ) := by
  obtain ⟨-, hM, hcop, hMb, hI, -⟩ := hd
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpI : (d.pd : 𝓞 D.host.E) ∈ d.I := GlobalTheory.CharacterFunction.natCast_mem_half hM hMb
  have hI0 : d.I ≠ ⊥ := fun e => by
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at hpI
    rw [hM, hpI, mul_zero] at hM₂
    exact lt_irrefl _ hM₂
  haveI : Finite (𝓞 D.host.E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I V.rank (Dw.rank.trans hrk)
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.TwistTie.exists_det_hom d.I (hrk ▸ hpq) e
  have hIJ : IsCoprime d.I (Mfr d.l₂) := by
    rw [Mfr, hMb, Ideal.map_mul]
    refine IsCoprime.mul_right ?_ (Ideal.isCoprime_iff_sup_eq.2 hI)
    obtain ⟨α, β, hαβ⟩ := Nat.Coprime.cast (R := 𝓞 D.host.E) hcop
    have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) (natCast_mem_Mb l)
    rw [map_natCast] at h1
    exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mul_mem_left _ α hpI, _, Ideal.mul_mem_left _ β h1, hαβ⟩
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := GlobalTheory.TwistTie.exists_basis_lift d.I (Mfr d.l₂) hIJ e
  let ρ : ∀ P : Q, (𝓞 D.host.E ⧸ d.I)ˣ →* (kP P.1)ˣ := fun P =>
    Units.map (Ideal.Quotient.factor (hQ P.1 P.2)).toMonoidHom
  let χ : (𝓞 D.host.E ⧸ d.I)ˣ →* ℂ := ∏ P : Q, (Units.coeHom ℂ).comp ((ch P.1).comp (ρ P))
  have hχ : ∀ x, χ x = ∏ P : Q, ((ch P.1 (ρ P x) : ℂˣ) : ℂ) := fun x => MonoidHom.finset_prod_apply _ _ _
  have hχF : ∀ x, χ x ∈ c.F := fun x => hχ x ▸ prod_mem fun P _ => hmem P.1 P.2 _
  refine ⟨((χ.codRestrict c.F hχF).toHomUnits).comp δ, fun k s u U hk hlift hU w hw => ?_⟩
  refine (hχ (δ k)).trans (Finset.prod_congr rfl fun P _ => congrArg (fun t => ((ch P.1 t : ℂˣ) : ℂ)) (Units.ext ?_))
  have hItop : d.I ≠ ⊤ := fun hT => P.1.isPrime.ne_top (top_le_iff.1 (hT ▸ hQ P.1 P.2))
  have hrange : (latG V 1 : Set (Fin V.rank → D.host.E)) = Set.range io := by
    rw [← hι.2, LinearMap.coe_range]
  obtain ⟨a, ha₁, ha₂⟩ := GlobalTheory.TwistTie.det_sub_mem_hat D.host.F io (hrange ▸ (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1) d.I hItop v hv₃ s
    d.l₂.M (by rw [hM, Nat.cast_mul]; exact d.I.mul_mem_left _ hpI) (finHom V u).1 (by
      rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers, ← hU]
      exact unswap_int U)
    (fun j => by
      rw [← hrange, ← (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1]
      exact hlift _ (hv₁ j))
  have hdet := hδ k a fun j => by
    rw [← hv₂, ← hk, (Submodule.Quotient.eq _).2 (ha₁ j), ← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hv₂]
  obtain ⟨Z, hZ, hZ0⟩ := resS_eq_zero (hQ P.1 P.2) ha₂
  have hUZ : U = Z + oToS _ _ a.det := by
    apply Subtype.ext
    rw [← swap_unswap U.1, Subring.coe_add, ← swap_unswap Z.1, hU, hZ, RingHom.map_sub]
    exact (sub_add_cancel _ _).symm
  rw [hw, hUZ, RingHom.map_add, hZ0, zero_add, resS_oToS]
  change Ideal.Quotient.factor (hQ P.1 P.2) (δ k : 𝓞 D.host.E ⧸ d.I) = _
  rw [hdet]
  rfl

set_option maxHeartbeats 1000000 in

theorem psiTie_of_values (V : HSp D) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ}
    (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : IotaOK Dw V io) (hpq : 1 ≤ Dw.p + Dw.q) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hd : d.IsLev) (hA₂ : d.l₂.A = 1) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ) (hN : 0 < N)
    (hxN : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hrat : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) (U₂ : _) (dict₂ : _) (c0 : ℂ) (hc0 : c0 ^ N = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ)
    (hψ : ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La), ∀ u ∈ GfC V, gLat V u = latHat V →
      (∀ a, (Submodule.Quotient.mk (s a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
      (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
        (finHom V u).1.mulVec (finVec V (io a)) - finVec V (io (s a)) = d.l₂.M • w) →
      (((ψ k : c.Fˣ) : c.F) : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) : d.PsiTie ψ := by
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := hd
  intro k g ρ hg _ hρ hk K _ _ _ y y' hy
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  obtain ⟨u, hu₀, hu, hlift⟩ := GlobalTheory.HalfLift.exists_unitary_inducing D H Dw d.l₂ V io hι (g.f d.l₂.M) g' fun a =>
    ⟨GlobalTheory.DatumInverseCharacter.mem_of_modN Dw (natCast_mem_Mb _) (hg' a).1,
      GlobalTheory.DatumInverseCharacter.mem_of_modN Dw (natCast_mem_Mb _) (hg' a).2⟩
  refine GlobalTheory.TwistTie.value_ratio V U₂ dict₂ io e₀ F ik φ th x₀ (RingHom.ext fun _ => rfl) hA₂ hpq hU hW hD hι hth
    (fun k τ hτ => ?_) d.cδ hsec c0 xi N hN hc0 hxN hval hrat g ρ hρ u
    (by unfold latGHat; rw [hu, GlobalTheory.TwistTie.gLat_one]) (fun b hb => ?_) _ (hψ k _ u hu₀ hu hk hlift) K y y' hy
  · rw [(hW k).1, (hU.2.1 k).1]
    exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)
  · obtain ⟨w, hw, ew⟩ := hlift b hb
    exact ⟨w, hw, sub_eq_iff_eq_add'.1 ew⟩

theorem exists_unitary_of_isometry (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V io)
    (s : Sim Dw) (hν : ∀ n, s.ν n = 1) : ∃ u : GA D V, gLat V u = latHat V ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1,
      (finHom V u).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw io hι.emb hι.isom s hν
  have hc := (GlobalTheory.Member.latG_move D V).2.2.2 1 κ (GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hκ.symm)
  rw [inv_one, one_mul] at hc
  exact ⟨κ, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, hκs⟩

section Pairing

open GlobalTheory.DatumInverseCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem cSep_sub_one_mem (l : Level H) : cSep l - 1 ∈ l.Mb := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (l.coprime.ge (Submodule.mem_top (x := (1 : 𝓞 E))))
    exact ⟨b, hb, by rw [← hab, sub_add_cancel_right]; exact neg_mem ha⟩
  unfold cSep
  rw [dif_pos h]
  exact h.choose_spec.2

theorem mem_of_pairing (l : Level H) {t : 𝓞 E} (ht : t - 1 ∈ l.Mb) {y : Dw.La}
    (h : ∀ q, (l.M : ℤ) ∣ Dw.EF y (t • q)) : y ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : (l.M : 𝓞 E) ∈ Mfr l := Ideal.mul_le_right (l.prod.ge (Ideal.mem_span_singleton_self _))
  have h1 : H.bar t • y ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
    mem_of_modN Dw hM (modN_of_dvd Dw (by have := l.three_le; omega) fun q => by rw [Dw.adj, bar_bar]; exact h q)
  have h2 : (H.bar t - 1) • y ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
    refine Submodule.smul_mem_smul ?_ trivial
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ht
    rwa [map_sub, map_one] at this
  have := sub_mem h1 h2
  rwa [sub_smul, one_smul, sub_sub_cancel] at this

theorem adjoint_eq {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hb : l₂.Mb ≤ l.Mb) (s : Sim Dw) (hν : ∀ n, s.ν n = 1)
    (σq : LevQ Dw l₂ → LevQ Dw l₂) (hσ : ∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f l₂.M a))
    (hlow : ∀ a, a - s.f l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) (x x' : Dw.La)
    (h : ∀ q, (l₂.M : ℤ) ∣ Dw.EF x (cSep l₂ • levRep (σq q)) - Dw.EF x' (cSep l₂ • levRep q)) :
    x - s.f l₂.M x' ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      s.f l₂.M x' - x' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
  have hc := cSep_mem l₂
  have hiso : ∀ q, (l₂.M : ℤ) ∣ Dw.EF (s.f l₂.M x') (cSep l₂ • s.f l₂.M q) - Dw.EF x' (cSep l₂ • q) := fun q => by
    have := s.mult l₂.M hM₂ x' (cSep l₂ • q)
    rwa [hν, one_mul, map_smul] at this
  constructor
  · refine mem_of_pairing l₂ (cSep_sub_one_mem l₂) fun q' => ?_
    obtain ⟨g, hg⟩ := s.inv l₂.M hM₂
    have h1 := h (Submodule.Quotient.mk (g q'))
    have h2 := dvd_right Dw l₂.prod hc x (w := levRep (σq (Submodule.Quotient.mk (g q'))) - s.f l₂.M (g q')) (by
      rw [← Submodule.Quotient.eq, levRep_spec, hσ])
    have h3 := dvd_right Dw l₂.prod hc x' (w := levRep (l := l₂) (Submodule.Quotient.mk (g q')) - g q') (by
      rw [← Submodule.Quotient.eq, levRep_spec])
    have h4 := dvd_right Dw l₂.prod hc (x - s.f l₂.M x') (mem_of_modN Dw (natCast_mem_Mb l₂) (hg q').2)
    have h5 := hiso (g q')
    simp only [smul_sub, map_sub, LinearMap.sub_apply] at h2 h3 h4 ⊢
    have := dvd_sub (dvd_sub (dvd_add (dvd_sub h1 h2) h3) h5) h4
    have e : ∀ a b c d e f g : ℤ, a - b - (a - c) + (b - d) - (e - d) - (c - e - (f - g)) = f - g := by
      intros; ring
    rwa [e] at this
  · refine mem_of_pairing l (hb (cSep_sub_one_mem l₂)) fun q => ?_
    have h1 := dvd_right Dw l.prod (Ideal.map_mono hb hc) (s.f l₂.M x') (hlow q)
    have h2 := (Int.natCast_dvd_natCast.2 hM).trans (hiso q)
    simp only [smul_sub, map_sub, LinearMap.sub_apply] at h1 ⊢
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

end Pairing

set_option maxHeartbeats 1000000 in

theorem datEq_of_values (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hβ : IsSDFrame T βT Λ 1) (e : AE D) {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c S.rank) (hd : d.IsLev)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (hι : IotaOK Dw T io) (Pg Q : Finset (Pl D.host.E))
    (hPg : ∀ P ∈ Pg, l.Mb ≤ P.asIdeal) (hQ : ∀ P ∈ Q, d.I ≤ P.asIdeal) (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ)
    (φ : (Fin S.rank → LevQc Dw d.l₂) → c.F) (w : (Fin S.rank → LevQ Dw d.l₂) → c.F)
    (hw : ∀ q, d.eF (w q) = phiHat d.c₂ (fun x => d.eF (φ x)) q)
    (hint : ∀ x : Fin S.rank → Dw.La, IsIntM (uMat S T βS βT e fun b => io (x b)))
    (hφ : ∀ x : Fin S.rank → Dw.La, ((φ fun b => Submodule.Quotient.mk (x b) : c.F) : ℂ) =
      omegaK Pg (fun P => redM P (uMat S T βS βT e fun b => io (x b))) *
        omegaQ Q T.rank ch (-1) (fun P => redM P (uMat S T βS βT e fun b => io (x b))))
    (ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ)
    (hψ : ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d)
      (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (u : GA D T) (U : Formalism.L2.Herm.intAf D.host.F D.host.E),
      (∀ a, (Submodule.Quotient.mk (s a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
      (∀ a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T 1,
        (finHom T u).1.mulVec (finVec T (io a)) - finVec T (io (s a)) = d.l₂.M • w) →
      unswap D U = (finHom T u).1.det → ∀ v : ∀ P : Q, (kP P.1)ˣ, (∀ P : Q, (v P : kP P.1) = resS D.host.F P.1 U) →
      (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P : Q, ((ch P.1 (v P) : ℂˣ) : ℂ)) : GlobalTheory.ClsVal.DatEq d ψ w := by
  refine GlobalTheory.ClsVal.datEq_of_phiHat _ H Dw l Xo c _ d hd ψ φ w hw fun kI σq σc h1 h2 x => ?_
  obtain ⟨-, hM, -, hMb, -⟩ := hd
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  obtain ⟨s, hν, hs, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing _ H Dw d.l₂ σq
  have hσ : ∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f d.l₂.M a) := fun a => (hs a).symm
  obtain ⟨u, hu, hus⟩ := exists_unitary_of_isometry T io hι s hν
  obtain ⟨y, hy, hdet⟩ := exists_int_matrix hβ hu
  have key := fun b => adjoint_eq (l := l) ⟨_, hM⟩ (hMb.le.trans Ideal.mul_le_left) s hν σq hσ (fun a => (h1 _ _ (hσ a)).1)
    (qRep (x b)) (qRep (σc.symm (x b))) fun q => by
      have := h2 (σc.symm (x b)) q
      rwa [LinearEquiv.apply_symm_apply] at this
  obtain ⟨X, e1, e2, hlow⟩ : ∃ X : Fin S.rank → Dw.La, ((fun b => σc.symm (x b)) = fun b => Submodule.Quotient.mk (X b)) ∧
      (x = fun b => Submodule.Quotient.mk (s.f d.l₂.M (X b))) ∧
      ∀ b, s.f d.l₂.M (X b) - X b ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
    ⟨fun b => qRep (σc.symm (x b)), funext fun b => (GlobalTheory.DatumInverseCharacter.qRep_spec _).symm, funext fun b =>
      (GlobalTheory.DatumInverseCharacter.qRep_spec _).symm.trans ((Submodule.Quotient.eq _).2 (key b).1), fun b => (key b).2⟩
  rw [e1]
  have hrange : (latG T 1 : Set (Fin T.rank → D.host.E)) = Set.range io := by
    rw [← hι.emb.2, LinearMap.coe_range]
  have hK : ∀ P ∈ Pg, redM P (uMat S T βS βT e fun b => io (X b)) =
      redM P (uMat S T βS βT e fun b => io (s.f d.l₂.M (X b))) := fun P hP =>
    GlobalTheory.redM_adj_congr D S T βS βT e _ io hint (Mfr l) P (fun a ha => by
      obtain ⟨t, ht, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) H.bar.surjective).1 ha
      exact ⟨t, hPg P hP ht, (star_star _).symm.trans (congrArg star (H.bar_eq t).symm)⟩) _ X hlow
  have hmove : ∀ P ∈ Q, redM P (uMat S T βS βT e fun b => io (X b)) =
      redM P (uMat S T βS βT e fun b => io (s.f d.l₂.M (X b))) * (Formalism.UG.bc (resS D.host.F P) y).1 := fun P hP =>
    GlobalTheory.AdjMove.redM_uMat_move D S T βS βT e _ io hint u y hy d.l₂.M P
      (hQ P hP (Ideal.mul_le_right (hMb.le (natCast_mem_Mb d.l₂)))) _ X fun b => by
        rw [← hrange, ← (GlobalTheory.T.adelicElementLattice_full_and_completion D T 1).2.2.2.2.1]
        exact hus _ hM₂ _
  have hval := hψ kI (s.f d.l₂.M) u y.1.det (fun a => (h1 _ _ (hσ a)).2.symm) (fun a _ => by
    obtain ⟨z, hz, ez⟩ := hus _ hM₂ a
    exact ⟨z, hz, sub_eq_iff_eq_add'.2 ez⟩) hdet
    (fun P => Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y))
    fun P => ((resS D.host.F P.1).map_det _).symm
  apply Subtype.ext
  rw [e2, IntermediateField.coe_mul, Units.val_inv_eq_inv_val, IntermediateField.coe_inv, hval, hφ, hφ,
    GlobalTheory.TwistDatumRight.omegaQ_mul_right D _ _ Q ch (fun P => Formalism.UG.bc (resS D.host.F P) y) _ _ hmove, Units.coe_prod, ← Finset.prod_coe_sort Q,
    mul_left_comm]
  congr 2
  unfold omegaK
  classical
  exact if_congr (forall₂_congr fun P hP => by beta_reduce; rw [hK P hP]) rfl rfl

set_option maxHeartbeats 2000000 in

theorem clsEx_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → GlobalTheory.OneMapTuples.ClsEx O (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ _ i Tp tup O hLL hO t x _
  have hT := tie.laws
  have hL := hR.lev
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr : 1 ≤ D.R.r := by
    have h1 := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2.1
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  obtain ⟨hd, hA₂, hnab⟩ := hO.cov t
  obtain ⟨-, -, hxi, ⟨e, -, hφ⟩, hMb, hQ, -⟩ := hO.tuple t
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨n, hn, ho⟩ := hL.xi_fin (tup t)
  obtain ⟨xi', hx1, -, hx3, hx4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi _) n hn ho
    (hL.xi_triv _) (hL.xi_tame _)
  have hxx : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨z, hz⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g z hz).trans (hx1 g z hz).symm)
  have hxN : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) ^ (m * n) = 1 := fun g => by
    rw [hxx, mul_comm, pow_mul, hx4, one_pow]
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  obtain ⟨gramR, c0R, c0L, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ⟩ := exists_psi (Wc D i) (O.dδ t) (iotaW T i) hio.emb (hpq.trans (rank_Wc i).symm) hpos hd (R.Q (tup t)) hQ
    (R.xiR (tup t)) fun P hP z =>
      hLL (GlobalTheory.RationalValues.xiR_mem R hL hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z)
  have htie : (O.dδ t).PsiTie ψ := by
    refine psiTie_of_values (Wc D i) (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      (fun γ hγ => (hxx γ).trans (hx3 γ hγ)) _ _ c0 hcN (hv t) ψ fun k s u hu₀ hu hk hlift => ?_
    obtain ⟨y, -, hdet⟩ := exists_int_matrix (hL.βW i) hu
    have hres : ∀ P : R.Q (tup t), ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y) : (kP P.1)ˣ) : kP P.1) =
        resS D.host.F P.1 y.1.det := fun P => ((resS D.host.F P.1).map_det _).symm
    obtain ⟨z, hz, hval⟩ := exists_root_value (O.dδ t).l₂ hu₀ (hL.xi (tup t)) (hL.xi_tame _) (R.Q (tup t)) (R.xiR (tup t))
      (hL.xiR _) (fun P hP => (hd.2.2.2.1.le.trans Ideal.mul_le_right).trans (hQ P hP)) (fun P => (hL.Q_ram _ P).1) _ hdet _ hres
    exact (hψ k s u _ hk hlift hdet _ hres).trans (hval.symm.trans (hxi u z hz).symm)
  have hτ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  obtain ⟨τ₀⟩ := hτ
  have hnV : (κ i).n = (Vc D i).rank := (tie.kap i τ₀).2.2.trans (D.sp.V_rank _ hj.1 hj.2).symm
  have hlast : (κ i).LastPos := fun τ k hk => by
    rw [(tie.kap i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    refine GlobalTheory.LiftWeight.one_le_aPl_last D i τ _ _ ?_ hk
    simp only [Ranks.sigW]
    omega
  obtain ⟨-, cga, -, -, hrange, -⟩ := hO.io
  exact GlobalTheory.ClsVal.exists_cusp_isThClsD_unique GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) _ _ hr
    (fun σ hσ' => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ')) hT.pins.2.1.2
    (fun _ => ⟨hd, hA₂, hnab⟩)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ (Wc D i) _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      _ _ c0 hcN (hv t))
    ψ htie _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) (hnV ▸ dom_wtA (κ i))
    (GlobalTheory.lastPos_wtA_of_pins D T.Q hT.pins _ hj _ hlast)
    (fun k => datEq_of_values (Vc D i) (Wc D i) (R.βV i) (R.βW i) (hL.βW i) e (O.dδ t) hd _ hio R.Pg (R.Q (tup t))
      (fun P hP => hMb.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hP))) hQ _ (O.φ t) _ (hO.w t k)
      (fun z => (hφ z).1) (fun z => (hφ z).2) ψ hψ)
    (hO.reps t).1 hrange.le x

end GlobalTheory.PinnedClassSum
