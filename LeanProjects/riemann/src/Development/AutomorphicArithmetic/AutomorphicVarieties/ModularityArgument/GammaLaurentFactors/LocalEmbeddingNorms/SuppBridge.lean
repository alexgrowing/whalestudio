import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedNeBotOfIsSubquotientOfIsCompact

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open GroundTheory.Automorphic.Parabolic (levi parabolicInd mem_levi leviUnipotent)
open scoped Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_int_one (g : GL (Fin 1) k) :
    g ∈ integralGL k 1 ↔ valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = g 0 0 := by simp [Matrix.det_unique]
  have h2 : (g⁻¹ : GL (Fin 1) k) 0 0 * g 0 0 = 1 := by
    have := congrFun (congrFun g.inv_mul 0) 0
    simpa [Matrix.mul_apply] using this
  have h3 := congrArg (valuation k) h2
  rw [map_mul, map_one] at h3
  rw [mem_integralGL_iff, h1]
  constructor
  · rintro ⟨a, b⟩
    have a' : valuation k (g 0 0) ≤ 1 := a 0 0
    have b' : valuation k ((g⁻¹ : GL (Fin 1) k) 0 0) ≤ 1 := b 0 0
    refine le_antisymm a' ?_
    calc 1 = _ := h3.symm
      _ ≤ 1 * valuation k (g 0 0) := by gcongr
      _ = _ := one_mul _
  · intro h
    rw [h, mul_one] at h3
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact h.le
    · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact h3.le

private theorem unram_iff {D : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ (GL (Fin D) k) Y)
    (hρ : IsSmooth ρ) (y : IrrRep (GL (Fin D) k)) (hy : IsSubquotient y.ρ ρ)
    (hc : D = 1 → ∀ g v, v ≠ 0 → ρ g v = v → ρ g = 1) :
    (∃ ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * 1)) ↔
      D = 1 ∧ ∀ g ∈ integralGL k D, ρ g = 1 := by
  have key : ∀ (hD : D = 1) ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ →
      ∀ g v, y.ρ g v = (ξ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    rintro rfl ξ hξ h g v
    have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) ξ) (isCuspidal_detRep_one hξ).1
        (isIrreducible_ofChar _) := h
    obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
    refine φ.toLinearEquiv.injective ?_
    refine (φ.toIntertwiningMap.isIntertwining _ _ g v).trans ?_
    rw [map_smul]
    simp [detRep]
    rfl
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  constructor
  · rintro ⟨ξ, hξ, h, hu⟩
    have hD : D = 1 := congrArg Sigma.fst h
    have k1 := key hD ξ hξ h
    subst hD
    rw [mul_one] at hu
    have hf : fixed y.ρ (integralGL k 1) ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
      rw [k1, hu _ ((mem_int_one g.1).1 g.2)]; simp, hv⟩
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ hρ hy
      (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k 1) hf)
    exact ⟨rfl, fun g hg => hc rfl g w hw0 (by simpa using hw ⟨g, hg⟩)⟩
  · rintro ⟨hD, h⟩
    obtain ⟨ξ, hξ, e⟩ : ∃ ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ := by
      subst hD
      obtain ⟨θ, hθ, e⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ y.ρ y.smooth y.irr
      exact ⟨θ, hθ, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 e)⟩
    have k1 := key hD ξ hξ e
    subst hD
    refine ⟨ξ, hξ, e, fun x hx => ?_⟩
    have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) x) = x := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    have h3 := h _ ((mem_int_one (Matrix.GeneralLinearGroup.scalar (Fin 1) x)).2 (by rw [h2, hx]))
    obtain ⟨S, f, hf⟩ := hy
    obtain ⟨w, rfl⟩ := hf v
    have h4 := k1 (Matrix.GeneralLinearGroup.scalar (Fin 1) x) (f w)
    have h5 : S.toRepresentation (Matrix.GeneralLinearGroup.scalar (Fin 1) x) w = w :=
      Subtype.ext (by show ρ _ _ = _; rw [h3]; rfl)
    rw [← f.isIntertwining, h5, h2] at h4
    have h6 : ((ξ x : ℂ) - 1) • f w = 0 := by rw [sub_smul, ← h4, one_smul, sub_self]
    have h7 := (smul_eq_zero.1 h6).resolve_right hv
    rw [mul_one]
    exact Units.ext (sub_eq_zero.1 h7)

private theorem cusp_block {n r : ℕ} {d : Fin r → ℕ} (e : (Σ j, Fin (d j)) ≃ Fin n) {β : Fin n → ℕ}
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (φ : Levi k (fun j => Fin (d j)) ≃* levi k n β)
    (hφ : ∀ g, ((φ g : levi k n β) : GL (Fin n) k) = leviEmb k e g) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi k n β) W) (hc : GroundTheory.Automorphic.Parabolic.IsCuspidal σ) (j : Fin r)
    {t : ℕ} {c : Fin t → ℕ} (e' : (Σ a, Fin (c a)) ≃ Fin (d j)) (hU : unipRad k e' ≠ ⊥) :
    Subsingleton (Jacquet ((σ.comp φ.toMonoidHom).comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W) (unipRad k e')) := by
  have hinj : Function.Injective fun p : Fin (d j) => e ⟨j, p⟩ := fun p q h => by simpa using h
  let γ : Fin n → ℕ := Function.extend (fun p : Fin (d j) => e ⟨j, p⟩) (fun p => (blk e' p).val) 0
  have γ1 : ∀ p, γ (e ⟨j, p⟩) = (blk e' p).val := fun p => hinj.extend_apply _ _ p
  have γ0 : ∀ a, a ≠ j → ∀ p, γ (e ⟨a, p⟩) = 0 := fun a ha p =>
    Function.extend_apply' _ _ _ (by
      rintro ⟨q, hq⟩
      exact ha (congrArg Sigma.fst (e.injective hq)).symm)
  obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
  have hs := hc γ ⟨e ⟨j, p⟩, e ⟨j, q⟩, le_antisymm (not_lt.1 fun h => by simpa using (hβ _ _).1 h)
    (not_lt.1 fun h => by simpa using (hβ _ _).1 h), by
      rw [γ1, γ1]; exact fun h => hpq.ne (Fin.ext h)⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
  have hw : w ∈ Representation.Coinvariants.ker (σ.comp (leviUnipotent k n β γ).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  refine Submodule.span_mono ?_ hw
  rintro _ ⟨⟨u, v⟩, rfl⟩
  obtain ⟨g, hg⟩ := φ.surjective u.1
  obtain ⟨hP, h1⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 u.2)
  rw [← hg, hφ] at hP h1
  have hg1 : g = Pi.mulSingle j (g j) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · rw [Pi.mulSingle_eq_of_ne ha]
      ext x y
      have := h1 (e ⟨a, x⟩) (e ⟨a, y⟩) (by rw [γ0 a ha, γ0 a ha])
      rw [leviEmb_apply_same] at this
      rw [this]
      simp [Matrix.one_apply]
  have hu : g j ∈ unipRad k e' := by
    refine mem_unipRad.2 ⟨mem_parab.2 fun x y hxy => ?_, fun a x y => ?_⟩
    · have := hP (show γ (e ⟨j, y⟩) < γ (e ⟨j, x⟩) by rw [γ1, γ1]; exact hxy)
      rwa [leviEmb_apply_same] at this
    · have := h1 (e ⟨j, e' ⟨a, x⟩⟩) (e ⟨j, e' ⟨a, y⟩⟩) (by rw [γ1, γ1]; simp)
      rw [leviEmb_apply_same] at this
      rw [this]
      simp [Matrix.one_apply]
  refine ⟨⟨g j, hu⟩, v, ?_⟩
  show σ u.1 v - v = σ (φ (Pi.mulSingle j (g j))) v - _
  rw [← hg1, hg]
  simp

private theorem cnt_eq {n r : ℕ} {d : Fin r → ℕ} (hd : ∀ j, 0 < d j) (e : (Σ j, Fin (d j)) ≃ Fin n) {β : Fin n → ℕ}
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (φ : Levi k (fun j => Fin (d j)) ≃* levi k n β)
    (hφ : ∀ g, ((φ g : levi k n β) : GL (Fin n) k) = leviEmb k e g) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} {s : Multiset (IrrGL k)} (hs : HasSupport π s)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi k n β) W) (hi : σ.IsIrreducible)
    (hc : GroundTheory.Automorphic.Parabolic.IsCuspidal σ) (ι : Representation.IntertwiningMap π (parabolicInd k n β σ))
    (hι : Function.Injective ι) :
    cnt s 1 = (Finset.univ.filter fun j => d j = 1 ∧ ∀ g ∈ integralGL k (d j), σ (φ (Pi.mulSingle j g)) = 1).card := by
  let τ : Representation ℂ (Levi k fun j => Fin (d j)) W := σ.comp φ.toMonoidHom
  have hστ : τ.comp φ.symm.toMonoidHom = σ := by
    ext g v
    simp [τ]
  have hτ : τ.IsIrreducible := by
    let o : Subrepresentation τ ≃o Subrepresentation σ :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          simpa [τ] using S.apply_mem_toSubmodule (φ.symm g) hv⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact (OrderIso.isSimpleOrder_iff o).2 hi
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd k e β hβ φ hφ τ
  rw [hστ] at E
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hs.isIrreducible
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f := E.symm.toIntertwiningMap.comp ι
  have hf : f v ≠ 0 := fun h => hv (hι (E.symm.toLinearEquiv.injective (by
    rw [map_zero, map_zero]; exact h)))
  have hτs : IsSubquotient τ (jac e π) := .of_surjective (GlobalTheory.CompanionTheory.FrobJm.frobMap e f)
    (GlobalTheory.CompanionTheory.FrobJm.surjective_of_ne_zero hτ _ (GlobalTheory.CompanionTheory.FrobJm.frobMap_ne_zero e f ⟨v, hf⟩))
  have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e hs.isSmooth)
  have hsm : ∀ j, IsSmooth (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) W) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j)) inferInstance
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hs e hτ hτs y hy
  have hu1 : ∀ j, u j = {IrrGL.of (y j).ρ (y j).smooth (y j).irr} := fun j => by
    refine SupportUnique.eq_singleton_of_isCusp (IrrGL.isCusp_of.2 ⟨hd j, (y j).smooth, fun t c e' hU => ?_⟩)
      ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    have h0 := cusp_block e hβ φ hφ σ hc j e' hU
    obtain ⟨S, g, hg⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e' (hsm j) (hy j)
    haveI : Subsingleton S.toSubmodule := ⟨fun a b => Subtype.ext (h0.elim _ _)⟩
    exact Function.Surjective.subsingleton hg
  suffices key : ∀ j, (∃ ξ hξ, IrrGL.of (y j).ρ (y j).smooth (y j).irr = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * 1)) ↔
      d j = 1 ∧ ∀ g ∈ integralGL k (d j), σ (φ (Pi.mulSingle j g)) = 1 by
    simp only [hu1]
    rw [← GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_univ_eq_sum, cnt, Multiset.filter_map, Multiset.card_map]
    rw [← Finset.filter_val, ← Finset.card_def]
    refine Finset.card_bij (fun j _ => j) ?_ (fun _ _ _ _ h => h) ?_ <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, key, exists_prop, exists_eq_right, imp_self, implies_true]
  intro j
  refine unram_iff _ (hsm j) (y j) (hy j) fun hD g w hw0 hw => ?_
  have hcomm : ∀ x : Levi k fun j => Fin (d j), Pi.mulSingle j g * x = x * Pi.mulSingle j g := fun x => by
    funext a
    by_cases ha : a = j
    · subst ha
      haveI : Unique (Fin (d a)) := hD ▸ inferInstance
      ext p q
      simp [Matrix.mul_apply, Subsingleton.elim p default, Subsingleton.elim q default, mul_comm]
    · simp [Pi.mulSingle_eq_of_ne ha]
  let K : Subrepresentation τ :=
    ⟨LinearMap.eqLocus (τ (Pi.mulSingle j g)) 1, fun x z hz => by
      have hz' : τ (Pi.mulSingle j g) z = z := hz
      show (τ (Pi.mulSingle j g) * τ x) z = τ x z
      rw [← map_mul, hcomm, map_mul, Module.End.mul_apply, hz']⟩
  haveI := hτ
  rcases eq_bot_or_eq_top K with h | h
  · have : w ∈ K.toSubmodule := hw
    rw [h] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) hw0
  · refine LinearMap.ext fun z => ?_
    have : z ∈ K.toSubmodule := by rw [h]; trivial
    exact this

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.Parabolic in
theorem UpperTheory.V.Z.Gam.suppBridge :
    UpperTheory.V.Z.Gam.SuppBridge := by
  intro F _ _ _ _ _ n V _ _ π s hs β W _ _ σ _ hi hc ι hι
  let o : Fin (Fintype.card (Set.range β)) ≃o Set.range β := monoEquivOfFin _ rfl
  let d := fun j => blockSize β (o j)
  let e : (Σ j, Fin (d j)) ≃ Fin n :=
    (Equiv.sigmaCongr o.toEquiv fun j => fiberFin β (o j)).trans (Equiv.sigmaFiberEquiv (blockOf β))
  have he : ∀ j p, e ⟨j, p⟩ = (fiberFin β (o j) p).1 := fun _ _ => rfl
  have hb : ∀ j p, β (e ⟨j, p⟩) = (o j).1 := fun j p => congrArg Subtype.val (fiberFin β (o j) p).2
  let ψ : levi F n β ≃* Levi F (fun j => Fin (d j)) :=
    { (leviEquivPi F β).toEquiv.trans
        (Equiv.piCongrLeft' (fun a => GL (Fin (blockSize β a)) F) o.symm.toEquiv) with
      map_mul' := fun x y => funext fun j => congrFun (map_mul (leviEquivPi F β) x y) (o j) }
  have hψ : ∀ m j, ψ m j = leviEquivPi F β m (o j) := fun _ _ => rfl
  have h := cnt_eq (d := d) (fun j => blockSize_pos β (o j)) e (β := β) (fun x y => by
    obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective y
    rw [hb, hb, blk_apply, blk_apply, Subtype.coe_lt_coe, o.lt_iff_lt]) ψ.symm (fun g => by
    obtain ⟨m, rfl⟩ := ψ.surjective g
    rw [ψ.symm_apply_apply]
    ext x y
    obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective y
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, hψ, leviEquivPi_apply, he, he]
    · rw [leviEmb_apply_ne _ _ _ hab]
      refine mem_levi.1 m.2 _ _ ?_
      rw [hb, hb]
      exact fun h => hab (o.injective (Subtype.ext h))) hs σ hi hc ι hι
  rw [h, cntF]
  refine Finset.card_equiv o.toEquiv fun j => ?_
  have hm : ∀ g, ψ.symm (Pi.mulSingle j g) = (leviEquivPi F β).symm (Pi.mulSingle (o j) g) := fun g => by
    rw [MulEquiv.symm_apply_eq]
    funext a
    rw [hψ, ContinuousMulEquiv.apply_symm_apply]
    by_cases ha : a = j
    · subst ha; simp
    · rw [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne (o.injective.ne ha)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hm]
  rfl
