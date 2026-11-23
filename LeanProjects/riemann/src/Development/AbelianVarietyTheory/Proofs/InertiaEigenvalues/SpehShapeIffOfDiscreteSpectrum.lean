import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SpehProductSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalUnitaryEmbeddingDefiniteUnitaryNonsplStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlaceStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.IndefiniteRowSideFullHecke.SpehProductSatake GlobalTheory.LFun
  GlobalTheory.PRep Formalism.UG

namespace GlobalTheory.BcSpehCompare

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

omit [IsTotallyComplex E] in

theorem isCompact_KGL : IsCompact (KGL w a : Set (GL (Fin a) (w.adicCompletion E))) :=
  IntPtsUnitary.isCompact_GLint _
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w))

theorem injective_of_irred {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {τ : G → W → W} (h0 : ∀ g, τ g 0 = 0) {f : V →ₗ[ℂ] W} (hf0 : f ≠ 0)
    (hf : ∀ g v, f (σ g v) = τ g (f v)) : Function.Injective f := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ).2 (LinearMap.ker f) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, h0]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hf0

theorem hasSat_iff {P : CuspSub E a} {σ : LocIrr w a} (h : P.IsLocComp w σ) (B : Multiset ℂˣ) :
    (CG.mk P).HasSat w B ↔ HasSatGL w σ.ρ B := by
  rw [CG.hasSat_mk]
  obtain ⟨f, h0, hf⟩ := h
  have hi := injective_of_irred σ.irred (τ := fun g => P.locRep w g) (fun _ => map_zero _) h0 hf
  have hfix : ∀ v ∈ fixed σ.ρ (KGL w a), f v ∈ fixed (P.locRep w) (KGL w a) := fun v hv =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  have hne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v => (map_ne_zero_iff f hi).2
  constructor
  · intro hB
    refine ⟨?_, fun v hv hv0 => (hB.2 _ (hfix v hv) (hne v hv0)).of_map f hf hi⟩
    obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have h1 : LinearMap.range f ⊓ fixed (P.locRep w) (KGL w a) ≠ ⊥ := fun e =>
      h0 (LinearMap.range_eq_bot.1 (LocEx.eq_bot_of_fixed P w isCompact_KGL hφ0 hφ _
        (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hf g v⟩) e))
    obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hi (by
      rw [hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩
  · intro hB
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    refine ⟨(Submodule.ne_bot_iff _).2 ⟨f v, hfix v hv, hne v hv0⟩, fun x hx hx0 => ⟨hx0, hx, hB.card, fun ϖ hϖ j hj => ?_⟩⟩
    have htop : LocUniq.isoPart σ.ρ (P.locRep w) = ⊤ := by
      have hm := Submodule.map_injective_of_injective P.V.injective_subtype
      rcases P.irred ((LocUniq.isoPart σ.ρ (P.locRep w)).map P.V.subtype) (Submodule.map_subtype_le _ _) (by
        rintro o _ ⟨x, hx, rfl⟩
        exact ⟨_, LocUniq.isoPart_op P w σ.ρ o hx, rfl⟩) with h1 | h1
      · have h3 : f v ∈ LocUniq.isoPart σ.ρ (P.locRep w) :=
          Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (P.locRep w)) ⟨v, rfl⟩
        rw [hm (h1.trans (Submodule.map_bot _).symm)] at h3
        exact absurd h3 (hne v hv0)
      · exact hm (h1.trans (Submodule.map_subtype_top _).symm)
    have hc := Final.GLintComm E w a
    have hT := Tj_mem_hecke (n := a) hϖ j
    let e := LocGL.idem (P.isSmooth_locRep w) (isCompact_KGL (w := w) (a := a))
    have key : ∀ y ∈ LocUniq.isoPart σ.ρ (P.locRep w),
        heckeVec (P.locRep w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y := fun y hy => by
      refine Submodule.iSup_induction _ (motive := fun y =>
        heckeVec (P.locRep w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y) hy ?_ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        have h1 : e (g.toLinearMap u) = g.toLinearMap (LocGL.idem σ.smooth isCompact_KGL u) :=
          (LocGL.map_idem σ.smooth _ _ g u).symm
        rw [h1, ← map_heckeVec hc hT g.toLinearMap fun k y => LinearMap.congr_fun (g.isIntertwining' k) y, ← map_smul]
        congr 1
        by_cases hu : LocGL.idem σ.smooth (isCompact_KGL (w := w) (a := a)) u = 0
        · simp [hu, heckeVec]
        · exact (hB.2 _ (LocGL.idem_mem _ _ u) hu).2.2.2 ϖ hϖ j hj
      · simp [heckeVec]
      · intro y z hy hz
        rw [map_add, smul_add, ← hy, ← hz]
        refine Eq.trans (finsum_congr fun _ => ?_)
          (finsum_add_distrib (finite_heckeVec hc hT _ (e y)) (finite_heckeVec hc hT _ (e z)))
        simp only [map_add, smul_add]
    have h2 := key x (htop ▸ Submodule.mem_top)
    rwa [show e x = x from LocGL.idem_of_mem _ _ hx] at h2

end Linear

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

theorem not_isSplitAt {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, e⟩
  have hw : ∀ k : E, w.valuation E (IsCMField.complexConj E k) = w.valuation E k := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
        w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have := w.isPrime
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top
    (GlobalTheory.FixedPrime.le_of_under_le w.asIdeal (fun x hx => ?_) _ (congrArg HeightOneSpectrum.asIdeal e).le)))
  rw [← w.valuation_lt_one_iff_mem (K := E)] at hx ⊢
  exact (hw x).symm.trans_lt hx

theorem isUnramU_of_hasSatAt {π : Submodule ℂ (UA E n → ℂ)} {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hval : ∀ x, Valued.v (s x) = Valued.v x)
    {ϖ : w.adicCompletion E} {q : ℕ} {α : Fin (n / 2) → ℂˣ} (h : HasSatAt π w s ϖ q α) : IsUnramU π w := by
  obtain ⟨b, hb, hJ, p, hp, σ, ⟨hσ, f, h0, h1, h2⟩, hS⟩ := h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨ι, -, hι, -⟩ := GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit E n w s hs hval (not_isSplitAt hs hval)
  have hsurj : Function.Surjective p := fun g => by
    have hg : cT s g.1.val * antiJ _ n * g.1.val = antiJ _ n := g.2
    have hm : b * g.1 * b⁻¹ ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      change cT s (b.val * g.1.val * (b⁻¹).val) * 1 * (b.val * g.1.val * (b⁻¹).val) = 1
      calc _ = cT s (b⁻¹).val * (cT s g.1.val * (cT s b.val * b.val) * g.1.val) * (b⁻¹).val := by
            simp only [cT_mul, Matrix.mul_assoc, Matrix.mul_one]
        _ = cT s (b.val * (b⁻¹).val) * (b.val * (b⁻¹).val) := by
            rw [hJ, hg, ← hJ]; simp only [cT_mul, Matrix.mul_assoc]
        _ = 1 := by rw [Units.mul_inv, cT_one, Matrix.mul_one]
    refine ⟨⟨_, (hι ⟨_, hm⟩).1⟩, Subtype.ext ?_⟩
    rw [hp, (hι _).2]
    group
  have hi : Function.Injective f := by
    choose t ht using hsurj
    exact injective_of_irred hσ (τ := fun g => RU E n (t g)) (fun _ => map_zero _) h0 fun g u => by
      rw [← h2, ht]
  refine ⟨f v, h1 v, (map_ne_zero_iff f hi).2 hv0, fun x hx hk => ?_⟩
  rw [← h2 ⟨x, hx⟩ v, GlobalTheory.LGrp.mem_fixed.1 hv _ ⟨(p _).2, ?_⟩]
  change (p ⟨x, hx⟩).val ∈ KGL w n
  rw [hp]
  exact mul_mem (mul_mem (inv_mem hb) hk) hb

theorem exists_hasSatAt
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) (hw : ¬ IsSplitAt w) (hu : IsUnramU π w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q ∧
        HasSatAt π w s ϖ q α := by
  obtain ⟨s, ϖ, q, h1, h2⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hE w) hw
  obtain ⟨α, h3⟩ := GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace E n w s ϖ q h1 h2 (GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms E n (GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets E n))
    (GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit E n w s h1 h2.2.1 hw) π hπ hu
  exact ⟨s, ϖ, q, α, h1, h2, h3⟩

theorem isNormalised_of_isCsd {P : CuspSub E a} (h : P.IsCsd) : GlobalTheory.DiscSpec.IsNormalised P := by
  intro φ hφ t g
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a P
  have h1 := CsdUnitary.dchi_theta hω h fun _ => (t : ℂ)
  have h2 : dchi ω (fun _ => (t : ℂ)) = 0 := by
    rw [show star (fun _ => (t : ℂ) : Cinf E) = fun _ => (t : ℂ) from funext fun _ => Complex.conj_ofReal t,
      map_neg] at h1
    linear_combination -h1 / 2
  have h3 := chiInf_expU ω fun _ => (t : ℂ)
  rw [h2, Complex.exp_zero] at h3
  have h4 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
  rw [show ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 from h3, one_mul] at h4
  rw [← h4]
  exact congrArg (fun x => φ.1 (x * g)) (cornerGL_scalar (sInf E) _)

def HasUnitarySpeh (P : CG E a) (d : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), ∃ (ρ : LocIrr w a) (σ : LocIrr w (d * a)), P.IsLoc w (Quotient.mk _ ρ) ∧
    IsUnitarisable ρ.ρ ∧ IsUnitarisable σ.ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred) d σ.ρ

theorem transport {π : Submodule ℂ (UA E n → ℂ)} {N N' : Fin c → ℕ} (e : N = N') (h : ∑ i, N i = n) (h' : ∑ i, N' i = n)
    (Q : Fin c → ∀ b, LocIrr w b → Prop) (S : ∀ i, LocIrr w (N i)) (hQ : ∀ i, Q i _ (S i))
    (hS : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w S)) :
    ∃ S' : ∀ i, LocIrr w (N' i), (∀ i, Q i _ (S' i)) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h' w S') := by
  subst e
  exact ⟨S, hQ, hS⟩

def SpehShape (π : Submodule ℂ (UA E n → ℂ)) : Prop :=
  ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
    (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
    (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
    ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

end CM

end GlobalTheory.BcSpehCompare

end
