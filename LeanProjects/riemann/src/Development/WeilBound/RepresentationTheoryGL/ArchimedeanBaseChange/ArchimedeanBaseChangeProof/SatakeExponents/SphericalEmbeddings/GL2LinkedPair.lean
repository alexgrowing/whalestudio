import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2Intertwining
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoUnramTwistOfNoInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.GL2LinkedPair

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

section Const

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def constInd (P : Subgroup (GL (Fin n) k)) (σ : Representation ℂ P W) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (w0 : W)
    (hw : ∀ p : P, σ p w0 = (detChar (Fin n) χ (p : GL (Fin n) k) : ℂ) • w0) : smoothPart (ind P σ) :=
  ⟨⟨fun x => (detChar (Fin n) χ x : ℂ) • w0, fun p x => by
      show (detChar (Fin n) χ ((p : GL (Fin n) k) * x) : ℂ) • w0 = σ p ((detChar (Fin n) χ x : ℂ) • w0)
      rw [map_smul, hw, map_mul, Units.val_mul, smul_smul, mul_comm]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (hχ.detChar (n := Fin n)) (one_mem _)) fun g hg => by
        have hg' : detChar (Fin n) χ g = 1 := hg
        apply Subtype.ext
        funext x
        show (detChar (Fin n) χ (x * g) : ℂ) • w0 = (detChar (Fin n) χ x : ℂ) • w0
        rw [map_mul, hg', mul_one])⟩

theorem constInd_apply (P : Subgroup (GL (Fin n) k)) (σ : Representation ℂ P W) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (w0 : W) (hw : ∀ p : P, σ p w0 = (detChar (Fin n) χ (p : GL (Fin n) k) : ℂ) • w0) (x : GL (Fin n) k) :
    (constInd P σ χ hχ w0 hw).1.1 x = (detChar (Fin n) χ x : ℂ) • w0 := rfl

theorem smInd_constInd (P : Subgroup (GL (Fin n) k)) (σ : Representation ℂ P W) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (w0 : W) (hw : ∀ p : P, σ p w0 = (detChar (Fin n) χ (p : GL (Fin n) k) : ℂ) • w0) (g : GL (Fin n) k) :
    smInd P σ g (constInd P σ χ hχ w0 hw) = (detChar (Fin n) χ g : ℂ) • constInd P σ χ hχ w0 hw := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show (detChar (Fin n) χ (x * g) : ℂ) • w0 = (detChar (Fin n) χ g : ℂ) • ((detChar (Fin n) χ x : ℂ) • w0)
  rw [map_mul, Units.val_mul, smul_smul, mul_comm]

end Const

section Two

abbrev dg (p : parab k (points (Fin 2))) : Fin 2 → kˣ := (leviTorus k (Fin 2)).symm (leviProj k (points (Fin 2)) p)

abbrev sB (χs : Fin 2 → kˣ →* ℂˣ) : Representation ℂ (parab k (points (Fin 2))) ℂ :=
  (twist ((ofChar (torusChar χs)).comp (leviTorus k (Fin 2)).symm.toMonoidHom)
    (deltaHalf k (fun _ : Fin 2 => Unit))).comp (leviProj k (points (Fin 2)))

theorem det_dg (p : parab k (points (Fin 2))) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin 2) k) = dg p 0 * dg p 1 := by
  rw [det_parab k (points (Fin 2)) p, Fin.prod_univ_two]
  rfl

theorem detChar_two (χ : kˣ →* ℂˣ) (p : parab k (points (Fin 2))) :
    detChar (Fin 2) χ (p : GL (Fin 2) k) = χ (dg p 0) * χ (dg p 1) := by
  rw [detChar_apply, det_dg, map_mul]

theorem deltaHalf_two (p : parab k (points (Fin 2))) :
    deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) =
      absPow k (1 / 2) (dg p 0) * absPow k (-1 / 2) (dg p 1) := by
  rw [deltaHalf_apply, Fin.prod_univ_two, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
  congr 2 <;> norm_num

theorem sB_two (χs : Fin 2 → kˣ →* ℂˣ) (p : parab k (points (Fin 2))) (z : ℂ) :
    sB χs p z = ((absPow k (1 / 2) (dg p 0) * absPow k (-1 / 2) (dg p 1) * χs 0 (dg p 0) * χs 1 (dg p 1) : ℂˣ) : ℂ) * z := by
  show ((deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂˣ) : ℂ) •
    ofChar (torusChar χs) (dg p) z = _
  rw [deltaHalf_two, ofChar_apply, torusChar_apply, Fin.prod_univ_two, smul_eq_mul]
  push_cast
  ring

end Two

section Linked

variable (k)

theorem cont_leviTorus_symm (m : ℕ) :
    Continuous ((leviTorus k (Fin m)).symm.toMonoidHom : Levi k (fun _ : Fin m => Unit) →* (Fin m → kˣ)) :=
  continuous_pi fun a => (continuous_glDet (R := k) (n := Unit)).comp (continuous_apply a)

variable {k}

theorem kinj_of_form {m : ℕ} (α : Fin m → ℂˣ)
    (l : IndSp (points (Fin m)) ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin m)).symm.toMonoidHom)
      →ₗ[ℂ] ℂ)
    (hK : ∀ g ∈ KO k (Fin m), ∀ f, l (iP (k := k) α g f) = l f) (hl : l ≠ 0) :
    ∀ v ∈ fixed (iP (k := k) α) (KO k (Fin m)), l v = 0 → v = 0 := by
  intro v hv hlv
  have hc := GlobalTheory.LocGL.isCompl_fixed_twKer (π := iP (k := k) α) (isSmooth_parInd _ _) (H := KO k (Fin m)) GlobalTheory.SplitFlip.isCompact_KO
  have htw : ∀ x ∈ twKer (iP (k := k) α) (KO k (Fin m)) 1, l x = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => l x = 0) ?_ (map_zero l) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hx
    rintro _ ⟨g, w, rfl⟩
    show l ((iP (k := k) α) (g : GL (Fin m) k) w - ((1 : KO k (Fin m) →* ℂˣ) g : ℂ) • w) = 0
    rw [map_sub, map_smul, hK g g.2 w]
    simp
  obtain ⟨w, hw, hlw⟩ : ∃ w ∈ fixed (iP (k := k) α) (KO k (Fin m)), l w ≠ 0 := by
    by_contra h
    push_neg at h
    apply hl
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := x))
    rw [map_add, h a ha, htw b hb, add_zero]
    rfl
  have hw0 : w ≠ 0 := fun h => hlw (by rw [h, map_zero])
  have e := PositivityTheory.Rg.BcB.N3.GL2Intertwining.kline α hv hw
  have e2 := congrArg l e
  rw [map_smul, map_smul, hlv, smul_zero, smul_eq_mul] at e2
  have hv1 : v.1.1 1 = 0 := (mul_eq_zero.1 e2.symm).resolve_right hlw
  rw [hv1, zero_smul] at e
  exact (smul_eq_zero.1 e).resolve_left (PositivityTheory.Rg.BcB.N3.GL2Intertwining.one_ne_zero_of_fixed α hw hw0)

end Linked

section LinkedMain

theorem unram_chi (b : ℂˣ) : IsUnram (unrChar k b * absPow k (1 / 2)) := fun x hx => by
  rw [MonoidHom.mul_apply, isUnram_unrChar k b x hx, isUnram_absPow k _ x hx, one_mul]

theorem key_law (a b : ℂˣ) (hL : unrChar k a = unrChar k b * absPow k 1) (t : kˣ) :
    (unrChar k b t : ℂ) * (absPow k (1 / 2) t : ℂ) = (absPow k (-1 / 2) t : ℂ) * (unrChar k a t : ℂ) := by
  rw [hL, MonoidHom.mul_apply, Units.val_mul]
  have e : (absPow k 1 t : ℂ) = (absPow k (1 / 2) t : ℂ) * (absPow k (1 / 2) t : ℂ) := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add]; norm_num
  have e2 : (absPow k (-1 / 2) t : ℂ) * (absPow k (1 / 2) t : ℂ) = 1 := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add]; norm_num
  rw [e]
  linear_combination -((unrChar k b t : ℂ) * (absPow k (1 / 2) t : ℂ)) * e2

set_option maxHeartbeats 1000000 in
theorem linked (a b : ℂˣ) (hL : unrChar k a = unrChar k b * absPow k 1) :
    ∃ T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a]), KInj k T := by
  set χ : kˣ →* ℂˣ := unrChar k b * absPow k (1 / 2) with hχdef
  have hχ : IsSmoothChar χ := isSmoothChar_of_isUnram (unram_chi b)
  have hχi : IsSmoothChar χ⁻¹ := isSmoothChar_of_isUnram fun x hx => by
    rw [MonoidHom.inv_apply, unram_chi b x hx, inv_one]

  have hw : ∀ p : parab k (points (Fin 2)), sB (fun i => unrChar k (![b, a] i)) p 1 =
      (detChar (Fin 2) χ (p : GL (Fin 2) k) : ℂ) • (1 : ℂ) := by
    intro p
    rw [sB_two, detChar_two, smul_eq_mul, mul_one, mul_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hχdef, MonoidHom.mul_apply,
      Units.val_mul]
    have := key_law a b hL (dg p 1)
    linear_combination -((absPow k (1 / 2) (dg p 0) : ℂ) * (unrChar k b (dg p 0) : ℂ)) * this
  let g : IndSp (points (Fin 2)) ((ofChar (torusChar fun i => unrChar k (![b, a] i))).comp
      (leviTorus k (Fin 2)).symm.toMonoidHom) :=
    constInd (parab k (points (Fin 2))) (sB fun i => unrChar k (![b, a] i)) χ hχ 1 hw
  have hg : ∀ h : GL (Fin 2) k, iP (k := k) ![b, a] h g = (detChar (Fin 2) χ h : ℂ) • g :=
    smInd_constInd _ _ χ hχ 1 hw
  have hg0 : g ≠ 0 := fun h0 => by
    have := congrArg (fun f : IndSp _ _ => f.1.1 1) h0
    simp [g, constInd_apply] at this

  let ρ : Representation ℂ (Levi k fun _ : Fin 2 => Unit) ℂ :=
    (ofChar (torusChar fun i => unrChar k (![a, b] i))).comp (leviTorus k (Fin 2)).symm.toMonoidHom
  have hts : IsSmoothChar (torusChar fun i => unrChar k (![a, b] i)) :=
    GlobalTheory.TorusEigenform.isSmoothChar_torusChar fun i => isSmoothChar_of_isUnram (isUnram_unrChar k _)
  have hρ : IsSmooth ρ := isSmooth_comp ((isSmooth_ofChar_iff _).2 hts) _ (cont_leviTorus_symm k 2)
  have hρ1 : ∀ m z, ρ m z = ((torusChar fun i => unrChar k (![a, b] i)) ((leviTorus k (Fin 2)).symm m) : ℂ) * z :=
    fun m z => ofChar_apply _ _ _
  have hℓ : (LinearMap.id : Module.Dual ℂ ℂ) ∈ smoothPart ρ.dual := by
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hρ 1).mem_nhds (by simp)) fun m hm => ?_)
    have hm' : ρ m 1 = 1 := hm
    rw [hρ1, mul_one] at hm'
    show ρ.dual m LinearMap.id = LinearMap.id
    refine LinearMap.ext fun z => ?_
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.id_comp, hρ1]
    simp only [map_inv, Units.val_inv_eq_inv_val, hm', inv_one, one_mul]
    rfl
  let ℓ0 : smoothPart ρ.dual := ⟨LinearMap.id, hℓ⟩
  let σ' : Representation ℂ (parab k (points (Fin 2))) (smoothPart ρ.dual) :=
    (twist (contra ρ) (deltaHalf k (fun _ : Fin 2 => Unit))).comp (leviProj k (points (Fin 2)))
  have hw' : ∀ p : parab k (points (Fin 2)), σ' p ℓ0 = (detChar (Fin 2) χ⁻¹ (p : GL (Fin 2) k) : ℂ) • ℓ0 := by
    intro p
    apply Subtype.ext
    refine LinearMap.ext fun z => ?_
    show ((deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂˣ) : ℂ) •
        (contra ρ (leviProj k (points (Fin 2)) p) ℓ0 : Module.Dual ℂ ℂ) z =
      (detChar (Fin 2) χ⁻¹ (p : GL (Fin 2) k) : ℂ) * z
    rw [contra_apply, hρ1]
    simp only [ℓ0, LinearMap.id_apply, smul_eq_mul, deltaHalf_two, detChar_two, map_inv, torusChar_apply,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, MonoidHom.inv_apply, hχdef,
      MonoidHom.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have key := key_law a b hL (dg p 0)
    have e2 : (absPow k (-1 / 2) (dg p 1) : ℂ) * (absPow k (1 / 2) (dg p 1) : ℂ) = 1 := by
      rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add]; norm_num
    push_cast
    have e0 : (absPow k (-1 / 2) (dg p 0) : ℂ) * (absPow k (1 / 2) (dg p 0) : ℂ) = 1 := by
      rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add]; norm_num
    have hneg : (-(1 / 2) : ℂ) = -1 / 2 := by ring
    field_simp
    rw [hneg]
    linear_combination ((absPow k (1 / 2) (dg p 0) : ℂ) ^ 2 * (unrChar k b (dg p 0) : ℂ) * z) * e2 +
      ((absPow k (1 / 2) (dg p 0) : ℂ) * z) * key + ((unrChar k a (dg p 0) : ℂ) * z) * e0
  let g' : IndSp (points (Fin 2)) (contra ρ) :=
    constInd (parab k (points (Fin 2))) σ' χ⁻¹ hχi ℓ0 hw'
  have hg' : ∀ h : GL (Fin 2) k, parInd (points (Fin 2)) (contra ρ) h g' = (detChar (Fin 2) χ⁻¹ h : ℂ) • g' :=
    smInd_constInd _ _ χ⁻¹ hχi ℓ0 hw'
  obtain ⟨Ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.2.2
    (points (Fin 2)) hρ
  let l : IndSp (points (Fin 2)) ρ →ₗ[ℂ] ℂ := ((Ψ g' : smoothPart (parInd (points (Fin 2)) ρ).dual) : Module.Dual ℂ _)
  have hl : ∀ (h : GL (Fin 2) k) f, l (parInd (points (Fin 2)) ρ h f) = (detChar (Fin 2) χ h : ℂ) * l f := by
    intro h f
    have e1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap h⁻¹ g'
    have e3 := congrArg (fun L : smoothPart (parInd (points (Fin 2)) ρ).dual => (L : Module.Dual ℂ _) f) e1
    simp only [contra_apply, inv_inv] at e3
    have e4 : l (parInd (points (Fin 2)) ρ h f) =
        ((Ψ.toLinearEquiv (parInd (points (Fin 2)) (contra ρ) h⁻¹ g') : smoothPart _) : Module.Dual ℂ _) f := e3.symm
    rw [e4, hg', LinearEquiv.map_smul]
    show (detChar (Fin 2) χ⁻¹ h⁻¹ : ℂ) * l f = _
    rw [detChar_apply, detChar_apply, MonoidHom.inv_apply]
    simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv]
  have hl0 : l ≠ 0 := by
    intro h0
    have : Ψ g' = 0 := Subtype.ext h0
    have h1 : g' = 0 := by
      have h3 : Ψ.toLinearEquiv g' = 0 := this
      calc g' = Ψ.toLinearEquiv.symm (Ψ.toLinearEquiv g') := (Ψ.toLinearEquiv.symm_apply_apply g').symm
        _ = 0 := by rw [h3, map_zero]
    have h2 := congrArg (fun f : IndSp (points (Fin 2)) (contra ρ) => ((f.1.1 1 : smoothPart ρ.dual) : Module.Dual ℂ ℂ) 1) h1
    simp [g', constInd_apply, ℓ0] at h2
  have hK : ∀ kk ∈ KO k (Fin 2), ∀ f, l (iP (k := k) ![a, b] kk f) = l f := by
    intro kk hkk f
    have := hl kk f
    have hdet : detChar (Fin 2) χ kk = 1 := by
      rw [detChar_apply]
      exact unram_chi b _ (GlobalTheory.InertSupp.Unram.valuation_det_KO hkk)
    rw [hdet, Units.val_one, one_mul] at this
    exact this
  let T0 : IndSp (points (Fin 2)) ρ →ₗ[ℂ] IndSp (points (Fin 2)) ((ofChar (torusChar fun i => unrChar k (![b, a] i))).comp
      (leviTorus k (Fin 2)).symm.toMonoidHom) :=
    { toFun := fun f => l f • g
      map_add' := fun x y => by rw [map_add, add_smul]
      map_smul' := fun c x => by rw [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply] }
  refine ⟨⟨T0, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => ?_
    show l (iP (k := k) ![a, b] h f) • g = iP (k := k) ![b, a] h (l f • g)
    rw [map_smul, hg, smul_smul, show l (iP (k := k) ![a, b] h f) = _ from hl h f, mul_comm]
  · intro v hv hT
    have hT' : l v • g = 0 := hT
    have hlv : l v = 0 := (smul_eq_zero.1 hT').resolve_right hg0
    exact kinj_of_form ![a, b] l hK hl0 v hv hlv

end LinkedMain

end PositivityTheory.Rg.BcB.N3.GL2LinkedPair
