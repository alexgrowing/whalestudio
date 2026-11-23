import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

noncomputable section

namespace ReciprocityTheory.Neutral.Bridge

open ReciprocityTheory.Gal

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]

def FinCd2 (rho : Representation R G M) : Prop :=
  Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)

def DualityFor (χ : G →* Rˣ) (rho : Representation R G M) (hrho : ContAction rho) : Prop :=
  Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧
    Function.Bijective (cupH0H2TwistedDual χ rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 χ rho (MonoidHom.id _))

theorem contAction_comp (e : G ≃ₜ* G') {rho : Representation R G' M} (h : ContAction rho) :
    ContAction (rho.comp (e : G →* G')) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  exact h.comp ((map_continuous e).prodMap continuous_id)

theorem card_H0_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H0 (rho.comp (e : G →* G'))) = Nat.card (H0 rho) := by
  have hinv : Representation.invariants (rho.comp (e : G →* G')) = rho.invariants := by
    ext v
    simp only [Representation.mem_invariants, MonoidHom.comp_apply]
    constructor
    · intro h g'
      simpa using h (e.symm g')
    · intro h g
      exact h _
  unfold H0
  rw [hinv]

theorem card_H1_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H1 (rho.comp (e : G →* G'))) = Nat.card (H1 rho) := by
  let φ : (G' → M) ≃ₗ[R] (G → M) := LinearEquiv.funCongrLeft R M e.toMulEquiv.toEquiv
  have hd : ∀ m, d0 (rho.comp (e : G →* G')) m = φ (d0 rho m) := fun m => rfl
  have hZ : (Z1 rho).map φ.toLinearMap = Z1 (rho.comp (e : G →* G')) := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨hyc, hy⟩, rfl⟩
      refine ⟨hyc.comp (map_continuous e), fun g h => ?_⟩
      show y (e (g * h)) = y (e g) + rho (e g) (y (e h))
      rw [map_mul]
      exact hy (e g) (e h)
    · rintro ⟨hfc, hf⟩
      refine ⟨f ∘ e.symm, ⟨hfc.comp (map_continuous e.symm), fun g h => ?_⟩, ?_⟩
      · have h2 := hf (e.symm g) (e.symm h)
        simp only [Function.comp_apply, map_mul]
        simpa [MonoidHom.comp_apply] using h2
      · funext g
        show f (e.symm (e g)) = f g
        simp
  have hB : (B1 rho).map φ.toLinearMap = B1 (rho.comp (e : G →* G')) := by
    unfold B1
    rw [← LinearMap.range_comp]
    congr 1
  let fZ : Z1 rho ≃ₗ[R] Z1 (rho.comp (e : G →* G')) :=
    (φ.submoduleMap (Z1 rho)).trans (LinearEquiv.ofEq _ _ hZ)
  unfold H1
  refine (Nat.card_congr (Submodule.Quotient.equiv _ _ fZ ?_).toEquiv).symm
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hB]
    exact ⟨z, hz, rfl⟩
  · intro hw
    rw [← hB] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨fZ.symm w, ?_, fZ.apply_symm_apply w⟩
    have h3 : ((fZ.symm w : Z1 rho) : G' → M) = y := by
      apply φ.injective
      rw [show φ y = (w : G → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy

theorem card_H2_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H2 (rho.comp (e : G →* G'))) = Nat.card (H2 rho) := by
  let φ1 : (G' → M) ≃ₗ[R] (G → M) := LinearEquiv.funCongrLeft R M e.toMulEquiv.toEquiv
  let φ : (G' × G' → M) ≃ₗ[R] (G × G → M) :=
    LinearEquiv.funCongrLeft R M (e.toMulEquiv.toEquiv.prodCongr e.toMulEquiv.toEquiv)
  have hZ : (Z2 rho).map φ.toLinearMap = Z2 (rho.comp (e : G →* G')) := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨hyc, hy⟩, rfl⟩
      refine ⟨hyc.comp ((map_continuous e).prodMap (map_continuous e)), fun g h k => ?_⟩
      show rho (e g) (y (e h, e k)) - y (e (g * h), e k) + y (e g, e (h * k)) - y (e g, e h) = 0
      rw [map_mul, map_mul]
      exact hy (e g) (e h) (e k)
    · rintro ⟨hfc, hf⟩
      refine ⟨fun q => f (e.symm q.1, e.symm q.2),
        ⟨hfc.comp (((map_continuous e.symm).comp continuous_fst).prodMk
          ((map_continuous e.symm).comp continuous_snd)), fun g h k => ?_⟩, ?_⟩
      · have h2 := hf (e.symm g) (e.symm h) (e.symm k)
        simp only [map_mul]
        simpa [MonoidHom.comp_apply] using h2
      · funext q
        show f (e.symm (e q.1), e.symm (e q.2)) = f q
        simp
  have hC : (contMaps R M G').map φ1.toLinearMap = contMaps R M G := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (show Continuous y from hy).comp (map_continuous e)
    · intro hf
      refine ⟨f ∘ e.symm, (show Continuous f from hf).comp (map_continuous e.symm), ?_⟩
      funext g
      show f (e.symm (e g)) = f g
      simp
  have hcomm : φ.toLinearMap ∘ₗ d1 rho = d1 (rho.comp (e : G →* G')) ∘ₗ φ1.toLinearMap := by
    refine LinearMap.ext fun c => funext fun p => ?_
    show rho (e p.1) (c (e p.2)) - c (e p.1 * e p.2) + c (e p.1) =
      rho (e p.1) (c (e p.2)) - c (e (p.1 * p.2)) + c (e p.1)
    rw [map_mul]
  have hB : (B2 rho).map φ.toLinearMap = B2 (rho.comp (e : G →* G')) := by
    unfold B2
    rw [← Submodule.map_comp, hcomm, Submodule.map_comp, hC]
  let fZ : Z2 rho ≃ₗ[R] Z2 (rho.comp (e : G →* G')) :=
    (φ.submoduleMap (Z2 rho)).trans (LinearEquiv.ofEq _ _ hZ)
  unfold H2
  refine (Nat.card_congr (Submodule.Quotient.equiv _ _ fZ ?_).toEquiv).symm
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hB]
    exact ⟨z, hz, rfl⟩
  · intro hw
    rw [← hB] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨fZ.symm w, ?_, fZ.apply_symm_apply w⟩
    have h3 : ((fZ.symm w : Z2 rho) : G' × G' → M) = y := by
      apply φ.injective
      rw [show φ y = (w : G × G → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy

private theorem nonempty_Hn_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) (m : ℕ) :
    Nonempty (Hn (rho.comp (e : G →* G')) (m + 1) ≃ Hn rho (m + 1)) := by
  let φk : ∀ k : ℕ, ((Fin k → G') → M) ≃ₗ[R] ((Fin k → G) → M) := fun k =>
    LinearEquiv.funCongrLeft R M (Equiv.piCongrRight fun _ => e.toMulEquiv.toEquiv)
  have hC : ∀ k, (Cn rho k).map (φk k).toLinearMap = Cn (rho.comp (e : G →* G')) k := by
    intro k
    unfold Cn
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (show Continuous y from hy).comp
        (continuous_pi fun i => (map_continuous e).comp (continuous_apply i))
    · intro hf
      refine ⟨fun x => f (fun i => e.symm (x i)), (show Continuous f from hf).comp
        (continuous_pi fun i => (map_continuous e.symm).comp (continuous_apply i)), ?_⟩
      funext g
      show f (fun i => e.symm (e (g i))) = f g
      simp
  have hd : ∀ k, (φk (k + 1)).toLinearMap ∘ₗ dn rho k =
      dn (rho.comp (e : G →* G')) k ∘ₗ (φk k).toLinearMap := by
    intro k
    refine LinearMap.ext fun f => funext fun g => ?_
    show dn rho k f (fun i => e (g i)) =
      dn (rho.comp (e : G →* G')) k (fun x => f (fun i => e (x i))) g
    unfold dn
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.comp_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    funext i
    simp only [Fin.contractNth]
    split_ifs <;> simp [map_mul]
  have hZ : (Zn rho (m + 1)).map (φk (m + 1)).toLinearMap = Zn (rho.comp (e : G →* G')) (m + 1) := by
    unfold Zn
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, ⟨hyC, hyK⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hC]
        exact ⟨y, hyC, rfl⟩
      · calc dn (rho.comp (e : G →* G')) (m + 1) (φk (m + 1) y)
            = φk (m + 1 + 1) (dn rho (m + 1) y) := (LinearMap.congr_fun (hd (m + 1)) y).symm
          _ = 0 := by rw [hyK, map_zero]
    · rintro ⟨hfC, hfK⟩
      refine ⟨(φk (m + 1)).symm f, ⟨?_, ?_⟩, (φk (m + 1)).apply_symm_apply f⟩
      · rw [← hC] at hfC
        obtain ⟨y, hy, hyf⟩ := hfC
        rw [← hyf]
        simpa using hy
      · apply (φk (m + 1 + 1)).injective
        rw [map_zero]
        calc φk (m + 1 + 1) (dn rho (m + 1) ((φk (m + 1)).symm f))
            = dn (rho.comp (e : G →* G')) (m + 1) (φk (m + 1) ((φk (m + 1)).symm f)) :=
              LinearMap.congr_fun (hd (m + 1)) _
          _ = 0 := by rw [LinearEquiv.apply_symm_apply]; exact hfK
  have hB : (Bn rho (m + 1)).map (φk (m + 1)).toLinearMap = Bn (rho.comp (e : G →* G')) (m + 1) := by
    show (Submodule.map (dn rho m) (Cn rho m)).map (φk (m + 1)).toLinearMap =
      Submodule.map (dn (rho.comp (e : G →* G')) m) (Cn (rho.comp (e : G →* G')) m)
    rw [← Submodule.map_comp, hd m, Submodule.map_comp, hC m]
  let fZ : Zn rho (m + 1) ≃ₗ[R] Zn (rho.comp (e : G →* G')) (m + 1) :=
    ((φk (m + 1)).submoduleMap (Zn rho (m + 1))).trans (LinearEquiv.ofEq _ _ hZ)
  unfold Hn
  refine ⟨(Submodule.Quotient.equiv _ _ fZ ?_).toEquiv.symm⟩
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hB]
    exact ⟨z, hz, rfl⟩
  · intro hw
    rw [← hB] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨fZ.symm w, ?_, fZ.apply_symm_apply w⟩
    have h3 : ((fZ.symm w : Zn rho (m + 1)) : (Fin (m + 1) → G') → M) = y := by
      apply (φk (m + 1)).injective
      rw [show φk (m + 1) y = (w : (Fin (m + 1) → G) → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy

theorem FinCd2.of_comp (e : G ≃ₜ* G') {rho : Representation R G' M} (h : FinCd2 (rho.comp (e : G →* G'))) :
    FinCd2 rho := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, fun n hn => ?_⟩
  · haveI := h0
    exact Nat.finite_of_card_ne_zero (by rw [← card_H0_comp_equiv e rho]; exact Nat.card_pos.ne')
  · haveI := h1
    exact Nat.finite_of_card_ne_zero (by rw [← card_H1_comp_equiv e rho]; exact Nat.card_pos.ne')
  · haveI := h2
    exact Nat.finite_of_card_ne_zero (by rw [← card_H2_comp_equiv e rho]; exact Nat.card_pos.ne')
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨f⟩ := nonempty_Hn_comp_equiv e rho m
    haveI := h3 (m + 1) hn
    exact f.symm.subsingleton

theorem DualityFor.of_comp (e : G ≃ₜ* G') (χ : G' →* Rˣ) {rho : Representation R G' M} (hrho : ContAction rho)
    (h : DualityFor (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (contAction_comp e hrho)) :
    DualityFor χ rho hrho := by
  obtain ⟨⟨h0⟩, h1, h2, h3, h4⟩ := h
  refine ⟨⟨(equivH2OfIso e (charRep χ) (charRep (χ.comp (e : G →* G'))) (fun _ _ => rfl)).trans h0⟩,
    ?_, ?_, ?_, ?_⟩
  · exact bijective_of_iso
      (equivH0OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupZeroTwo_equiv e χ rho) h1
  · exact bijective_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h2
  · exact bijective_flip_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h3
  · exact bijective_of_iso
      (equivH2OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH0OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupTwoZero_equiv e χ rho) h4

end ReciprocityTheory.Neutral.Bridge
