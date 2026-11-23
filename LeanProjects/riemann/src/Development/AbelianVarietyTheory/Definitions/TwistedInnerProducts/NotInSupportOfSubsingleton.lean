import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def evalOne (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : π.IntertwiningMap (parInd e ρ)) : (jac e π).IntertwiningMap ρ where
  toLinearMap := (twKer π (unipRad k e) 1).liftQ
    { toFun := fun v => (f v).1.1 1
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp } (Submodule.span_le.2 (by
      rintro _ ⟨u, v, rfl⟩
      have h1 := parInd_law e ρ (f v) ⟨u, unipRad_le_parab k e u.2⟩ 1
      rw [(coe_mem_unipRad k ⟨u, unipRad_le_parab k e u.2⟩).1 u.2] at h1
      have h2 : (f (π u v)).1.1 1 = (f v).1.1 (1 * u) := by rw [f.isIntertwining]; rfl
      show (f (π u v - _)).1.1 1 = 0
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.coe_sub, Pi.sub_apply]
      rw [h2]
      simp only [map_one, Units.val_one, one_smul, mul_one, one_mul, Module.End.one_apply] at h1 ⊢
      rw [h1, sub_self]))
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    have h1 := parInd_law e ρ (f v) ⟨_, leviEmb_mem_parab k e g⟩ 1
    rw [leviProj_leviEmb] at h1
    have h2 : (f (π (leviEmb k e g) v)).1.1 1 = (f v).1.1 (1 * leviEmb k e g) := by
      rw [f.isIntertwining]; rfl
    show (f ((((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • π (leviEmb k e g) v)).1.1 1 = ρ g ((f v).1.1 1)
    rw [map_smul]
    show (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • (f (π (leviEmb k e g) v)).1.1 1 = ρ g ((f v).1.1 1)
    rw [h2, one_mul]
    simp only [mul_one] at h1
    rw [h1, smul_smul]
    simp

theorem evalOne_bijective (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    (ρ : Representation ℂ (Levi k m) W) :
    Function.Bijective (evalOne e : π.IntertwiningMap (parInd e ρ) → _) := by
  constructor
  · intro f f' h
    ext v x
    have h1 : ∀ f : π.IntertwiningMap (parInd e ρ),
        (f v).1.1 x = evalOne e f (Submodule.Quotient.mk (π x v)) := fun f => by
      show _ = (f (π x v)).1.1 1
      rw [f.isIntertwining, parInd_apply, one_mul]
    exact (h1 f).trans (h ▸ (h1 f').symm)
  · intro φ
    refine ⟨⟨{ toFun := fun v => ⟨⟨fun x => φ (Submodule.Quotient.mk (π x v)), fun p x => ?_⟩, ?_⟩
               map_add' := fun v w => ?_
               map_smul' := fun c v => ?_ }, fun g => ?_⟩, ?_⟩
    · obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
      show φ (Submodule.Quotient.mk (π (p * x) v)) =
        (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (φ (Submodule.Quotient.mk (π x v)))
      have hq : (Submodule.Quotient.mk (π u (π x v)) : Jacquet π (unipRad k e)) =
          Submodule.Quotient.mk (π x v) :=
        (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨u, hu⟩, π x v, by simp⟩)
      rw [← φ.isIntertwining, ← hq, jac_mk, map_smul, smul_smul]
      conv_lhs => rw [hp]
      simp
    · refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => ?_)
      have hg' : π g v = v := hg
      apply Subtype.ext
      funext x
      show φ (Submodule.Quotient.mk (π (x * g) v)) = φ (Submodule.Quotient.mk (π x v))
      simp [hg']
    · ext x; simp
    · ext x; simp
    · ext v x
      show φ (Submodule.Quotient.mk (π x (π g v))) = φ (Submodule.Quotient.mk (π (x * g) v))
      simp
    · apply Representation.IntertwiningMap.ext
      refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
      show φ (Submodule.Quotient.mk (π 1 v)) = φ (Submodule.Quotient.mk v)
      simp

theorem scalar_of_isSubquotient {G : Type} [Group G] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) {g : G} {c : ℂ} (hc : ∀ v, ρ g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨v, rfl⟩ := hf w
  rw [← f.isIntertwining, ← map_smul]
  congr 1
  exact Subtype.ext (hc v)

theorem nontrivial_of_isIrreducible {G : Type} [Group G] {σ : Representation ℂ G W}
    (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  have : (⊥ : Subrepresentation σ) = ⊤ :=
    Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

theorem jac_detRep (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) (g : Levi k m)
    (x : Jacquet (detRep n χ) (unipRad k e)) : jac e (detRep n χ) g x = (detLevi e χ g : ℂ) • x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [jac_mk]
  show _ • Submodule.Quotient.mk (ofChar _ _ v) = _
  rw [ofChar_apply, ← smul_eq_mul, Submodule.Quotient.mk_smul, smul_smul]
  simp [detLevi, mul_comm]

theorem inSupport_detRep_iff {N : ℕ} (χ ψ : kˣ →* ℂˣ) :
    InSupport (detRep (Fin N) χ) ψ ↔
      ∃ i : Fin N, ψ = χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) := by
  refine ⟨?_, fun ⟨i, h⟩ => h ▸ inSupport_detRep χ i⟩
  rintro ⟨s, d, e, a, ha, Y, _, _, σ, hσ, hsub, hact⟩
  have hN : ∑ b, d b = N := by simpa using Fintype.card_congr e
  have hsplit : ∑ b, d b = (∑ b with b < a, d b) + d a + ∑ b with a < b, d b := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_ite_eq_of_mem Finset.univ a d (Finset.mem_univ a),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne', h.not_gt]
    · simp [h]
    · simp [h, h.ne, h.not_gt]
  refine ⟨⟨∑ b with b < a, d b, by omega⟩, MonoidHom.ext fun x => ?_⟩
  have := nontrivial_of_isIrreducible hσ
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  let g : GL (Fin (d a)) k := GeneralLinearGroup.scalar _ x
  have hg : GeneralLinearGroup.det g = x := by
    ext; simp [g, GeneralLinearGroup.scalar, ha]
  have h1 := scalar_of_isSubquotient hsub (jac_detRep e χ (Pi.mulSingle a g)) y
  rw [hact, hg, detLevi_apply, Finset.prod_eq_single a, Pi.mulSingle_eq_same, hg] at h1
  · have h2 := Units.ext (smul_left_injective ℂ hy h1)
    rw [h2]
    congr 3
    have h3 : (N : ℂ) = ((∑ b with b < a, d b : ℕ) : ℂ) + 1 + ((∑ b with a < b, d b : ℕ) : ℂ) := by
      rw [← hN, hsplit, ha]; push_cast; ring
    simp only [modExp, Fintype.card_fin, h3]
    push_cast
    ring
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one, map_one]
  · simp

theorem inSupport_one_iff (χ ψ : kˣ →* ℂˣ) : InSupport (detRep (Fin 1) χ) ψ ↔ ψ = χ := by
  simp [inSupport_detRep_iff]

theorem not_inSupport_zero (π : Representation ℂ (GL (Fin 0) k) V) (ψ : kˣ →* ℂˣ) : ¬ InSupport π ψ := by
  rintro ⟨s, d, e, a, ha, -⟩
  exact (e ⟨a, ⟨0, by omega⟩⟩).elim0

theorem not_inSupport_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL n k) V)
    (ψ : kˣ →* ℂˣ) : ¬ InSupport π ψ := by
  rintro ⟨s, d, e, a, ha, Y, _, _, σ, hσ, ⟨S, f, hf⟩, -⟩
  have := nontrivial_of_isIrreducible hσ
  have : Subsingleton (Jacquet π (unipRad k e)) := (Submodule.Quotient.mk_surjective _).subsingleton
  exact not_subsingleton Y hf.subsingleton

theorem jhMult_ofChar_ne {G : Type} [Group G] {χ ψ : G →* ℂˣ} (h : χ ≠ ψ) :
    jhMult (ofChar χ) (ofChar ψ) = 0 := by
  refine le_antisymm (iSup₂_le fun r ⟨S, T, _, _, hr⟩ => ?_) bot_le
  rcases r with _ | r
  · simp
  · exfalso
    obtain ⟨φ⟩ := hr 0
    refine h (MonoidHom.ext fun g => Units.ext ?_)
    obtain ⟨x, hx⟩ := φ.surjective 1
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := LinearMap.congr_fun (φ.isIntertwining' g) (Submodule.Quotient.mk v)
    have h2 : subQuot (S 0) (T 0) g (Submodule.Quotient.mk v) = (ψ g : ℂ) • Submodule.Quotient.mk v := by
      rw [← Submodule.Quotient.mk_smul]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (ofChar_apply ψ g _))
    simp only [LinearMap.comp_apply, h2, map_smul] at h1
    have hx' : φ.toLinearMap (Submodule.Quotient.mk v) = 1 := hx
    rw [hx'] at h1
    simpa using h1.symm

theorem modulus_two (ϖ : 𝒪[k]) (x : kˣ) (h : Irreducible ϖ) (hx : (x : k) = ϖ) :
    modulus k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) ![x, 1]) = (resCard k : ℝ)⁻¹ := by
  rw [modulus_torus, ← (nabs_properties k).2.2.2.2.1 ϖ x h hx]
  simp [Fin.prod_univ_two, Finset.prod_filter]

open NumberField IsDedekindDomain in

theorem completion (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    IsSpherical (detRep (Fin 2) (1 : (v.adicCompletion F)ˣ →* ℂˣ)) ∧
      ¬ IsCuspidal (detRep (Fin 2) (1 : (v.adicCompletion F)ˣ →* ℂˣ)) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  exact ⟨isSpherical_detRep fun _ _ => rfl, not_isCuspidal_detRep_two _⟩

theorem not_inSupport_of_isCuspidal [Nontrivial n] {π : Representation ℂ (GL n k) V} (h : IsCuspidal π)
    (ψ : kˣ →* ℂˣ) : ¬ InSupport π ψ := by
  rintro ⟨s, d, e, a, ha, Y, _, _, σ, hσ, ⟨S, f, hf⟩, -⟩
  have := nontrivial_of_isIrreducible hσ
  have key : ∀ i j : n, blk e i < blk e j → unipRad k e ≠ ⊥ := fun i j hij hb => by
    have hne : i ≠ j := fun h => hij.ne (h ▸ rfl)
    let u : GL n k := GeneralLinearGroup.mkOfDetNeZero (transvection i j 1)
      (by rw [det_transvection_of_ne i j hne]; exact one_ne_zero)
    have hu : u ∈ unipRad k e := by
      refine mem_unipRad.2 ⟨mem_parab.2 fun x y hxy => ?_, fun b x y => ?_⟩
      · show (transvection i j (1 : k)) x y = 0
        have h1 : x ≠ y := fun h => hxy.ne (h ▸ rfl)
        have h2 : ¬ (i = x ∧ j = y) := by
          rintro ⟨rfl, rfl⟩; exact hij.not_gt hxy
        simp [transvection, h1, single_apply, h2]
      · show (transvection i j (1 : k)) _ _ = _
        have h2 : ¬ (i = e ⟨b, x⟩ ∧ j = e ⟨b, y⟩) := by
          rintro ⟨rfl, rfl⟩; simp at hij
        simp [transvection, single_apply, h2, Matrix.one_apply]
    rw [hb, Subgroup.mem_bot] at hu
    have : (transvection i j (1 : k)) i j = (1 : Matrix n n k) i j :=
      congrArg (fun g : GL n k => (g : Matrix n n k) i j) hu
    simp [transvection] at this
  have hne : unipRad k e ≠ ⊥ := by
    obtain ⟨j, hj⟩ := exists_ne (e ⟨a, ⟨0, by omega⟩⟩)
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact key (e ⟨a, ⟨0, by omega⟩⟩) (e ⟨b, j⟩) (by simpa using hab)
    · exact absurd (by congr; ext; have := j.2; simp; omega) hj
    · exact key (e ⟨b, j⟩) (e ⟨a, ⟨0, by omega⟩⟩) (by simpa using hab)
  have := h.2 s d e hne
  exact not_subsingleton Y hf.subsingleton

theorem isCuspSupport_detRep {N : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspSupport (detRep (Fin N) χ) (fun _ : Fin N => 1)
      fun i => detRep (Fin 1) (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique _ _
  refine ⟨isIrreducible_ofChar _, fun i => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one
    (hχ.mul (isSmoothChar_of_isUnram (isUnram_absPow k _)))⟩, e, ?_⟩
  let f : (ofChar (detLevi e χ)).IntertwiningMap (piTensor fun i : Fin N =>
      detRep (Fin 1) (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2))) :=
    ⟨LinearMap.toSpanSingleton ℂ _ (PiTensorProduct.tprod ℂ fun _ => 1), fun g => by
      ext
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, piTensor_tprod,
        ofChar_apply, mul_one, detRep]
      rw [detLevi_apply, Units.coe_prod, ← MultilinearMap.map_smul_univ]
      congr 1
      funext i
      rw [modExp_fin _ (fun _ => by simp), smul_eq_mul, mul_one, detChar_apply]
      congr 4
      push_cast
      ring⟩
  have hf : Function.Injective f := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ fun h => ?_)
    have := congrArg (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ)) h
    simp at this
  refine (isSubquotient_detRep_parInd e hχ).trans (.of_injective (parIndMap e f) fun φ ψ h => ?_)
  ext x
  exact hf (congrFun (congrArg (fun t => t.1.1) h) x)

theorem hasSatake_one_unique {π : Representation ℂ (GL (Fin 1) k) V} {a b : Fin 1 → ℂˣ}
    (ha : HasSatake π a) (hb : HasSatake π b) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    a = b := by
  have key : ∀ {a : Fin 1 → ℂˣ}, HasSatake π a → ∀ v, π (diagT k (Fin 1) fun _ => ϖ) v = (a 0 : ℂ) • v := by
    intro a ha
    refine scalar_of_isSubquotient ha.2.2 fun f => ?_
    ext x
    have h1 := parInd_law (points (Fin 1)) _ f ⟨_, leviEmb_mem_parab k _ (leviTorus k _ fun _ => ϖ)⟩ x
    rw [leviProj_leviEmb] at h1
    have hc : x * (diagT k (Fin 1) fun _ => ϖ) = (diagT k (Fin 1) fun _ => ϖ) * x := by
      ext i j
      simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
    show f.1.1 (x * (diagT k (Fin 1) fun _ => ϖ)) = (a 0 : ℂ) • f.1.1 x
    rw [hc]
    refine h1.trans ?_
    have hm : modExp (fun _ : Fin 1 => Unit) 0 = 0 := by rw [modExp_fin _ (fun _ => by simp)]; simp
    simp [deltaHalf_apply, hm, unrChar_uniformizer k _ hϖ]
  have := nontrivial_of_isIrreducible ha.1
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  funext i
  rw [Subsingleton.elim i 0]
  exact Units.ext (smul_left_injective ℂ hy ((key ha y).symm.trans (key hb y)))

end GlobalTheory.SmGL.Model
