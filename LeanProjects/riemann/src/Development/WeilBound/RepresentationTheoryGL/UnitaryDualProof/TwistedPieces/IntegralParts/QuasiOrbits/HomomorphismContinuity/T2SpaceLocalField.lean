import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.SupportedComposition.ProjectionOfOrbitClosure
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbitRepresentatives.Reps0
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusHeights.StepModH
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.ModBoundT

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil Set Polynomial

namespace PositivityTheory.RgUd.TP.Nil.Orb.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil
open PositivityTheory.RgUd.T.Nil.Orb (GzS orb stab modul act_mul act_one)
open PositivityTheory.RgUd.T.Nil.Orb.Oasm (exists_open_orbit isClosed_Bz isNilpotent_iff_pow comp_mem_supportedIn orb_subset_UU
  action_mem_orbit_closure)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

local instance t2SpaceLocalField : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable (k) in

def ModH : Prop :=
  TraceForm k → ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ (p : Sp k n) (P : GL (Fin n) k)
    (w : Fin n → ℤ), p.1 ∈ Bz Z → IsNilpotent p.1 → p.2 ≠ 0 →
    (∀ t : kˣ, let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) →
    (∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) →
    ∃ a : ℝ, 2 * a < dB0 Z ∧ ∀ t : kˣ, nabs k t < 1 → ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧
      L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      g.val = P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a

section Hom

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_hom (t : kˣ) (p : Sp k n) : hom t⁻¹ (hom t p) = p := by
  refine Prod.ext ?_ rfl
  simp [hom, smul_smul]

theorem continuous_hom (t : kˣ) : Continuous (hom (n := n) t) :=
  (continuous_fst.const_smul (t : k)).prodMk continuous_snd

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := hom t
  invFun := hom t⁻¹
  left_inv p := hom_hom t p
  right_inv p := by simpa using hom_hom t⁻¹ p
  continuous_toFun := continuous_hom t
  continuous_invFun := continuous_hom t⁻¹

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_act (t : kˣ) (g : GL (Fin n) k) (p : Sp k n) : hom t (act g p) = act g (hom t p) := by
  simp only [hom, act]
  refine Prod.ext ?_ rfl
  simp only [mul_smul_comm, smul_mul_assoc]

theorem comp_hom_mem (t : kˣ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) :=
  comp_mem_supportedIn (homH t) hf

theorem invU_pullH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : InvU Z ξ) : InvU Z (pullH t ξ) := by
  intro g hg f hf
  show ξ (fun p => f (act g (hom t p))) = ξ (fun p => f (hom t p))
  have e : (fun p => f (act g (hom t p))) = fun p => (fun q => f (hom t q)) (act g p) := by
    funext p; show f (act g (hom t p)) = f (hom t (act g p)); rw [hom_act]
  rw [e]
  exact hξ g hg _ (comp_hom_mem t hf)

theorem invU_sub_smul {ξ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h1 : InvU Z ξ) (h2 : InvU Z η) (a : ℂ) : InvU Z (ξ - a • η) := by
  intro g hg f hf
  simp [h1 g hg f hf, h2 g hg f hf]

theorem kills_pullH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU) : Kills (pullH t ξ) UU :=
  fun f hf => hξ _ (comp_hom_mem t hf)

theorem kills_aevalH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU) (Q : ℂ[X]) :
    Kills (aeval (pullH (n := n) t) Q ξ) UU := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => intro f hf; simp [hp f hf, hq f hf]
  | monomial m a =>
    intro f hf
    have key : ∀ m : ℕ, Kills (((pullH (n := n) t) ^ m : Module.End ℂ _) ξ) UU := by
      intro m
      induction m with
      | zero => simpa using hξ
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact kills_pullH t ih
    simp [aeval_monomial, key m f hf]

theorem aeval_X_subH (t : kˣ) (a : ℂ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) :
    aeval (pullH (n := n) t) (X - Polynomial.C a) ξ = pullH t ξ - a • ξ := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem kills_of_suppU {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} {D : Set (Sp k n)} (hD : D ∩ UU = ∅) (h : SuppU ξ D) :
    Kills ξ UU := by
  intro f hf
  refine h f hf fun q hq => ?_
  by_contra hfq
  have : q ∈ D ∩ UU := ⟨hq, hf.2 hfq⟩
  rw [hD] at this
  exact this

theorem isClosed_NB : IsClosed (NB Z ×ˢ (Set.univ : Set (Fin n → k))) := by
  have : NB Z = Bz Z ∩ {x | x ^ n = 0} := by
    ext x; simp [NB, isNilpotent_iff_pow]
  rw [this]
  exact (isClosed_Bz.inter (isClosed_eq (continuous_id.pow n) continuous_const)).prod isClosed_univ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_mem_NB (hZ : CR Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) {q : Sp k n}
    (hq : q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k))) : act g q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)) := by
  have h := action_mem_orbit_closure hZ (zero_mem Z) hg (q := q) ⟨hq.1.1, by simpa using hq.1.2⟩
  exact ⟨⟨h.1, by simpa using h.2⟩, mem_univ _⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_mem_NB (t : kˣ) {q : Sp k n} (hq : q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k))) :
    hom t q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)) := by
  refine ⟨⟨fun a ha => ?_, hq.1.2.smul _⟩, mem_univ _⟩
  show a * ((t : k) • q.1) = (t : k) • q.1 * a
  rw [mul_smul_comm, smul_mul_assoc, hq.1.1 a ha]

end Hom

section Main

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem main_ind (h4 : StepModH k) (hZ : CR Z) (t : kˣ) (mm : Sp k n → ℂ) (s : Finset (Sp k n))
    (hs : ∀ p ∈ s, p.2 ≠ 0 ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k), g ∈ Gz Z ∧ act g p = hom t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      ((modul (stab Z p) K L g : ℝ) : ℂ) = mm p) :
    ∀ (N : ℕ) (T : Finset (Sp k n)), T.card ≤ N → T ⊆ s → ∀ D : Set (Sp k n), IsClosed D →
      (∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) → (∀ q ∈ D, hom t q ∈ D) → D ∩ UU ⊆ ⋃ p ∈ T, orb Z p →
      ∀ ξ, InvU Z ξ → SuppU ξ D → ∀ Q : ℂ[X], (∏ p ∈ T, (X - Polynomial.C (mm p))) ∣ Q →
        Kills (aeval (pullH (n := n) t) Q ξ) UU := by
  classical
  intro N
  induction N with
  | zero =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hT)
    subst hT0
    have hD0 : D ∩ UU = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => ?_
      simpa using hcov hq
    exact kills_aevalH t (kills_of_suppU hD0 hS) Q
  | succ N ih =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    by_cases hne : (D ∩ UU).Nonempty
    swap
    · exact kills_aevalH t (kills_of_suppU (Set.not_nonempty_iff_eq_empty.1 hne) hS) Q
    obtain ⟨p₀, hp₀T, hO, hcl⟩ := exists_open_orbit T (fun p hp => (hs p (hTs hp)).1) D hD hinv hcov hne
    obtain ⟨hp₀2, K, L, g, hg, hgp, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hm⟩ := hs p₀ (hTs hp₀T)
    set O := orb Z p₀ with hOdef
    set U := (UU : Set (Sp k n)) ∩ (D \ O)ᶜ with hUdef
    have hU : IsOpen U := PositivityTheory.RgUd.T.Nil.Orb.Oasm.isOpen_UU.inter hcl.isOpen_compl
    have hUD : U ∩ D = O := by
      ext q
      constructor
      · rintro ⟨⟨_, hqn⟩, hqD⟩
        by_contra hqO
        exact hqn ⟨hqD, hqO⟩
      · intro hqO
        exact ⟨⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩, hO hqO⟩
    have hstep := h4 n Z hZ t p₀ g hg hgp hp₀2 K hK hKo hKc L hLo hLKK hLn1 hLn2 D U hD hU hUD hinv hsig ξ hξ hS
    have hDU : D \ U = D \ O := by
      ext q
      constructor
      · rintro ⟨hqD, hqU⟩
        refine ⟨hqD, fun hqO => hqU ⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩⟩
      · rintro ⟨hqD, hqO⟩
        exact ⟨hqD, fun h => h.2 ⟨hqD, hqO⟩⟩
    rw [hDU, hm] at hstep
    have hOinv : ∀ h ∈ Gz Z, ∀ q, act h q ∈ O → q ∈ O := by
      rintro h hh q ⟨g', hg', hg'q⟩
      refine ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', ?_⟩
      rw [act_mul, hg'q, ← act_mul, inv_mul_cancel, act_one]
    have hsig0 : hom t⁻¹ p₀ = act g⁻¹ p₀ := by
      have e1 : hom t⁻¹ (act g p₀) = p₀ := by rw [hgp, hom_hom]
      rw [hom_act] at e1
      calc hom t⁻¹ p₀ = act g⁻¹ (act g (hom t⁻¹ p₀)) := by rw [← act_mul, inv_mul_cancel, act_one]
        _ = act g⁻¹ p₀ := by rw [e1]
    have hsigO : ∀ q, hom t q ∈ O → q ∈ O := by
      rintro q ⟨g', hg', hg'q⟩
      refine ⟨g' * g⁻¹, (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg), ?_⟩
      rw [act_mul, ← hsig0, ← hom_act, hg'q, hom_hom]
    set T' := T.filter (fun p => orb Z p ≠ O) with hT'def
    have hT'sub : T' ⊆ T.erase p₀ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_erase.2 ⟨fun h => hp.2 (by rw [h]), hp.1⟩
    have hT'card : T'.card ≤ N := by
      have := Finset.card_le_card hT'sub
      rw [Finset.card_erase_of_mem hp₀T] at this
      omega
    obtain ⟨Q0, hQ0⟩ := hQ
    set R := (∏ p ∈ T.erase p₀, (X - Polynomial.C (mm p))) * Q0 with hRdef
    have hQR : Q = R * (X - Polynomial.C (mm p₀)) := by
      rw [hQ0, ← Finset.mul_prod_erase T _ hp₀T, hRdef]
      ring
    have hT'R : (∏ p ∈ T', (X - Polynomial.C (mm p))) ∣ R :=
      dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ hT'sub) Q0
    have key : aeval (pullH (n := n) t) Q ξ = aeval (pullH (n := n) t) R (pullH t ξ - mm p₀ • ξ) := by
      rw [hQR, map_mul, Module.End.mul_apply, aeval_X_subH]
    rw [key]
    refine ih T' hT'card (fun p hp => hTs (Finset.mem_of_mem_filter p hp)) (D \ O) hcl ?_ ?_ ?_ _
      (invU_sub_smul (invU_pullH t hξ) hξ _) hstep R hT'R
    · rintro h hh q ⟨hqD, hqO⟩
      exact ⟨hinv h hh q hqD, fun h' => hqO (hOinv h hh q h')⟩
    · rintro q ⟨hqD, hqO⟩
      exact ⟨hsig q hqD, fun h' => hqO (hsigO q h')⟩
    · rintro q ⟨⟨hqD, hqO⟩, hqU⟩
      obtain ⟨p, hpT, hqp⟩ := Set.mem_iUnion₂.1 (hcov ⟨hqD, hqU⟩)
      refine Set.mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨hpT, fun h => hqO (h ▸ hqp)⟩, hqp⟩

end Main

section Final

variable (k) in

theorem orbQ_of (h3 : Reps0 k) (h4 : StepModH k) (h5 : ModH k) : OrbQ k := by
  classical
  intro hT _ n Z hZ hd t ht
  obtain ⟨s, hs, hcov⟩ := h3 n Z hZ
  have H : ∀ p ∈ s, ∃ a : ℝ, 2 * a < dB0 Z ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      g ∈ Gz Z ∧ act g p = hom t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := by
    intro p hp
    obtain ⟨hp1, hpn, hp2, P, w, hgr, hpos⟩ := hs p hp
    obtain ⟨a, ha, hat⟩ := h5 hT n Z hZ hd p P w hp1 hpn hp2 hgr hpos
    obtain ⟨K, L, g, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hgval, hmod⟩ := hat t ht
    have hgr' := hgr t
    simp only [← hgval] at hgr'
    obtain ⟨hgZ, hE, hv⟩ := hgr'
    have hgG : g ∈ Gz Z := fun b hb => hgZ b hb
    have e1 : g.val * p.1 * g⁻¹.val = (t : k) • p.1 := by
      rw [hE, smul_mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hact : act g p = hom t p := Prod.ext e1 hv
    exact ⟨a, ha, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩
  choose! a ha hKLg using H
  refine ⟨s.toList.map a, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ha p (Finset.mem_toList.1 hp)
  · intro ξ hsupp hinv
    set mm : Sp k n → ℂ := fun p => (((nabs k t)⁻¹ ^ a p : ℝ) : ℂ) with hmm
    have hprod : (polyH t (s.toList.map a) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) =
        aeval (pullH (n := n) t) (∏ p ∈ s, (X - Polynomial.C (mm p))) := by
      unfold polyH
      rw [← Finset.prod_map_toList s (fun p => X - Polynomial.C (mm p)), map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp only [mm, Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hprod]
    refine main_ind h4 hZ t mm s ?_ s.card s le_rfl subset_rfl (NB Z ×ˢ Set.univ) isClosed_NB
      (fun h hh q hq => act_mem_NB hZ hh hq) (fun q hq => hom_mem_NB t hq) ?_ ξ hinv hsupp _ dvd_rfl
    · intro p hp
      obtain ⟨K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩ := hKLg p hp
      exact ⟨(hs p hp).2.2.1, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, by rw [hmod]⟩
    · rintro q ⟨⟨⟨hq1, hqn⟩, -⟩, hqU⟩
      obtain ⟨p, hp, hqp⟩ := hcov q.1 hq1 hqn q.2 hqU
      exact Set.mem_iUnion₂.2 ⟨p, hp, hqp⟩

example : ModH k := PositivityTheory.RgUd.TP.Nil.Orb.modBound0 k

end Final

end PositivityTheory.RgUd.TP.Nil.Orb.Asm
