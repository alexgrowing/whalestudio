import Formalism.LocalToGlobal.GroupLattices.FockModels.NablaLTwEqMap

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Sub

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [Field K'] [Algebra R' K']
  {φK : K →+* K'}
  {X X' : Type} [AddCommGroup X] [Module K X] [Module R X] [IsScalarTower R K X]
  [AddCommGroup X'] [Module K' X'] [Module R' X'] [IsScalarTower R' K' X']
  (μ : X →ₛₗ[φK] X') (Vs : Submodule K X) (Vs' : Submodule K' X') (hV : ∀ z ∈ Vs, μ z ∈ Vs')

def muV : Vs →ₛₗ[φK] Vs' where
  toFun := fun x => ⟨μ x.1, hV _ x.2⟩
  map_add' := by intro x y; exact Subtype.ext (map_add μ x.1 y.1)
  map_smul' := by intro c x; exact Subtype.ext (map_smulₛₗ μ c x.1)

theorem muV_coe (x : Vs) : ((muV μ Vs Vs' hV x : Vs') : X') = μ x.1 := rfl

theorem bc_comap (A : Submodule R X) (A' : Submodule R' X') (hA : ∀ z ∈ A, z ∈ Vs) (h : BC μ A A') :
    BC (muV μ Vs Vs' hV) (A.comap (Vs.subtype.restrictScalars R)) (A'.comap (Vs'.subtype.restrictScalars R')) := by
  unfold BC
  apply le_antisymm
  · intro v' hv'
    have hv2 : (v' : X') ∈ A' := hv'
    have hmap : (Submodule.span R' (muV μ Vs Vs' hV '' ((A.comap (Vs.subtype.restrictScalars R) :
        Submodule R Vs) : Set Vs))).map (Vs'.subtype.restrictScalars R') = A' := by
      rw [h, Submodule.map_span, ← Set.image_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hA z hz⟩, hz, rfl⟩
    rw [← hmap] at hv2
    obtain ⟨y, hy, hye⟩ := hv2
    have : y = v' := Subtype.ext hye
    rw [← this]
    exact hy
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h.mem hx

theorem span_muV_top (h : BC μ Vs Vs') {I : Type} (x : Module.Basis I K Vs) :
    ⊤ ≤ Submodule.span K' (Set.range fun i => muV μ Vs Vs' hV (x i)) := by
  intro v' _
  have hv : (v' : X') ∈ Submodule.span K' (μ '' (Vs : Set X)) := by
    have h2 : Vs' ≤ Submodule.span K' (μ '' (Vs : Set X)) := le_of_eq h
    exact h2 v'.2
  have hle : Submodule.span K' (μ '' (Vs : Set X)) ≤
      (Submodule.span K' (Set.range fun i => muV μ Vs Vs' hV (x i))).map Vs'.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨muV μ Vs Vs' hV ⟨z, hz⟩, ?_, rfl⟩
    have h1 : (⟨z, hz⟩ : Vs) ∈ Submodule.span K (Set.range x) := by rw [x.span_eq]; trivial
    have h2 := (bc_span (muV μ Vs Vs' hV) (Set.range x)).mem h1
    rw [← Set.range_comp] at h2
    exact h2
  obtain ⟨y, hy, hye⟩ := hle hv
  have : y = v' := Subtype.ext hye
  rw [← this]
  exact hy

end Sub

section Dual

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [Field K'] [Algebra R' K']
  (φ : R →+* R') (φK : K →+* K') (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))
  {V V' : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K' V'] [Module R' V'] [IsScalarTower R' K' V']
  (ν : V →ₛₗ[φK] V') {I : Type} [Fintype I] (x : Module.Basis I K V) (x' : Module.Basis I K' V')
  (hx : ∀ i, x' i = ν (x i))

def deltaS : Module.Dual K V →ₛₗ[φK] Module.Dual K' V' where
  toFun := fun G => x'.constr K' fun i => φK (G (x i))
  map_add' := by
    intro a b
    apply x'.ext
    intro i
    rw [LinearMap.add_apply, Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis,
      LinearMap.add_apply, map_add]
  map_smul' := by
    intro c a
    apply x'.ext
    intro i
    rw [LinearMap.smul_apply, Module.Basis.constr_basis, Module.Basis.constr_basis, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, map_mul]

include hx in
theorem deltaS_apply (G : Module.Dual K V) (F : V) : deltaS φK x x' G (ν F) = φK (G F) := by
  have h1 : ν F = ∑ i, φK (x.repr F i) • x' i := by
    conv_lhs => rw [← x.sum_repr F]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hx]
  have h2 : G F = ∑ i, x.repr F i * G (x i) := by
    conv_lhs => rw [← x.sum_repr F]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  rw [h1, h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  congr 1
  exact Module.Basis.constr_basis x' K' _ i

include hφ hx in
theorem dual_mem (A : Submodule R V) (A' : Submodule R' V') (h : BC ν A A') (G : Module.Dual K V)
    (hG : G ∈ dualLat R K A) : deltaS φK x x' G ∈ dualLat R' K' A' := by
  intro v' hv'
  rw [h] at hv'
  induction hv' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hG z hz
    exact ⟨φ a, by rw [deltaS_apply φK ν x x' hx, ← ha, hφ]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha⟩ := hy
    exact ⟨c * a, by rw [LinearMap.map_smul_of_tower, map_mul, ha, Algebra.smul_def]⟩

theorem scale_mem {A : Submodule R V} {A' : Submodule R' V'} (h : ∀ y ∈ A, ν y ∈ A') (c : K) {y : V}
    (hy : y ∈ scale c A) : ν y ∈ scale (φK c) A' := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨ν z, h z hz, (map_smulₛₗ ν c z).symm⟩

end Dual

section Lat

variable {W Qq O Kf O' Kf' : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
  [CommRing O'] [IsDomain O'] [Field Kf'] [Algebra O' Kf']
  (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (φ : O →+* O') (φK : Kf →+* Kf')
  (hφ : ∀ x : O, φK (algebraMap O Kf x) = algebraMap O' Kf' (φ x))

theorem bc_extO (s : ℕ) {k : ℕ} (L : Submodule W (Fin k → Qq)) :
    BC (vecS φ φK hφ k) (extO O ι σ s L) (extO O' (φK.comp ι) σ s L) := by
  have h0 := bc_span (vecS φ φK hφ k) (twistVec ι σ s '' (L : Set (Fin k → Qq)))
  rw [Set.image_image] at h0
  exact h0

theorem bc_LeAt (p : ℕ) (w : O) (s : ℕ) {k : ℕ} (e : Edge W Qq k) :
    BC (vecS φ φK hφ k) (LeAt p ι σ w s e) (LeAt p (φK.comp ι) σ (φ w) s e) := by
  have h0 := bc_span (vecS φ φK hφ k) (twistVec ι σ s '' (e.src : Set (Fin k → Qq)) ∪
    (fun v => (algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v)) '' (e.tgt : Set (Fin k → Qq)))
  rw [Set.image_union, Set.image_image, Set.image_image, Submodule.span_union, Submodule.span_union] at h0
  have h1 : ∀ v : Fin k → Qq, vecS φ φK hφ k ((algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v)) =
      (algebraMap O' Kf' (φ w))⁻¹ • twistVec (φK.comp ι) σ s ((p : W) • v) := by
    intro v
    funext i
    show φK ((algebraMap O Kf w)⁻¹ * twistVec ι σ s ((p : W) • v) i) = _
    rw [map_mul, map_inv₀, hφ]
    rfl
  simp only [h1] at h0
  exact h0

theorem bc_Hten (hinj : Function.Injective (algebraMap O Kf)) (hinj' : Function.Injective (algebraMap O' Kf'))
    {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (Λ' : Fin n' → Submodule O' (Fin (m + 1) → Kf'))
    (hΛ : ∀ s, IsLattice O (Λ s)) (hb : ∀ s, BC (vecS φ φK hφ (m + 1)) (Λ s) (Λ' s)) :
    BC (MvPolynomial.map φK) (Hten O lam0 Λ) (Hten O' lam0 Λ') :=
  bc_tensorLat φ φK hφ _ _ fun s =>
    base_change_H0 φ φK hφ hinj hinj' m _ (kp_lamAt_antitone lam0 hd s) _ _ (hΛ s) (hb s)

theorem Hten_le_V {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s)) :
    ∀ z ∈ Hten O lam0 Λ, z ∈ Vsp Kf lam0 := by
  have hle : Hten O lam0 Λ ≤ (Vsp Kf lam0).restrictScalars O := by
    unfold Hten tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone lam0 hd s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    obtain ⟨g, hg, hge⟩ := hΛ s
    rw [hge] at h1
    exact la_nablaLTw_le _ _ _ hg _ (H0_le_twisted_nabla _ _ hanti _ hg h1)
  exact fun z hz => hle hz

theorem bc_Vsp {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) :
    BC (MvPolynomial.map φK) (Vsp Kf lam0) (Vsp Kf' lam0) := by
  unfold Vsp
  refine bc_tensorLat φK φK (fun _ => rfl) _ _ fun s => ?_
  have hanti := kp_lamAt_antitone lam0 hd s
  beta_reduce
  rw [if_pos hanti, if_pos hanti]
  exact bc_dualWeyl φK _ _ _

end Lat

theorem Vsp_bot (K : Type) [Field K] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : ¬ IsDominant lam0) :
    Vsp K lam0 = ⊥ := by
  unfold IsDominant at hd
  push Not at hd
  obtain ⟨s, hs⟩ := hd
  have hs' : ¬ Antitone (lamAt lam0 s) := by
    unfold lamAt
    split_ifs with he
    · exact hs
    · intro ha
      apply hs
      intro a b hab
      have h1 := ha (Fin.rev_le_rev.2 hab)
      simp only [Fin.rev_rev] at h1
      exact neg_le_neg_iff.1 h1
  unfold Vsp tensorLat
  rw [Submodule.span_eq_bot]
  rintro _ ⟨F, hF, rfl⟩
  have h2 := hF s
  beta_reduce at h2
  rw [if_neg hs'] at h2
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [(Submodule.mem_bot _).1 h2, map_zero]

theorem be_sum {Kf O : Type} [Field Kf] [CommRing O] [Algebra O Kf] {n' m : ℕ} (p r : ℕ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) {n : ℕ} (c : Fin n → O)
    (G : Fin n → Module.Dual Kf (Vsp Kf lam0)) :
    be p r lam0 F (∑ l, c l • G l) = ∑ l, algebraMap O Kf (c l) * be p r lam0 F (G l) := by
  unfold be
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [LinearMap.smul_apply, Algebra.smul_def]

section Main

variable {p n' : ℕ} {W Qq O Kf O' Kf' : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf'] [Algebra O' Kf']
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {φ : O →+* O'} {φK : Kf →+* Kf'}

theorem lpAt_nondom (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : ¬ IsDominant lam0) (t D : ℕ) (κ : ℝ)
    (cStar : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) :
    LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 0, ?_, 0, 0,
    fun _ j => j.elim0⟩
  have h0 : dimV Kf lam0 = 0 := by
    unfold dimV
    rw [Vsp_bot Kf lam0 hd]
    exact finrank_bot _ _
  rw [h0]
  simp

theorem lpAt_dom (hφ : ∀ x : O, φK (algebraMap O Kf x) = algebraMap O' Kf' (φ x))
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hS' : HidaSetting p n' W Qq O' Kf' (φK.comp ι) σ (φ.comp j) (φ w))
    (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
    (L : Submodule W (Fin (m + 1) → Qq)) (hL : IsLattice W L)
    (h : LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L) :
    LPprimeAt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t D κ cStar L := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := haveI := hS.frac_O; IsFractionRing.injective O Kf
  have hinj' : Function.Injective (algebraMap O' Kf') := haveI := hS'.frac_O; IsFractionRing.injective O' Kf'
  have bV := bc_Vsp φK lam0 hd
  set μ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₛₗ[φK]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf' := muS φK φK (fun _ => rfl) _ with hμ
  have hV : ∀ z ∈ Vsp Kf lam0, μ z ∈ Vsp Kf' lam0 := fun z hz => bV.mem hz
  set ν := muV μ (Vsp Kf lam0) (Vsp Kf' lam0) hV with hν
  have hlatE : ∀ (s : ℕ) (A : Submodule W (Fin (m + 1) → Qq)), IsLattice W A → IsLattice O (extO O ι σ s A) :=
    fun s A hA => je_extO_lat (mkG hS m r lam0 hd) (0 : Fin 1) s A hA
  have hlatL : ∀ (s : ℕ) (e : Edge W Qq (m + 1)), IsEdge p n' r e → IsLattice O (LeAt p ι σ w s e) :=
    fun s e he => je_LeAt_lat (mkG hS m r lam0 hd) (0 : Fin 1) s e he
  have hHL : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A →
      BC ν (HL (O := O) ι σ lam0 A) (HL (O := O') (φK.comp ι) σ lam0 A) := fun A hA =>
    bc_comap μ _ _ hV _ _ (Hten_le_V lam0 hd _ fun s => hlatE s.val A hA)
      (bc_Hten φ φK hφ hinj hinj' lam0 hd _ _ (fun s => hlatE s.val A hA) fun s => bc_extO ι σ φ φK hφ s.val A)
  have hHLe : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
      BC ν (HLe (O := O) p ι σ w lam0 e) (HLe (O := O') p (φK.comp ι) σ (φ w) lam0 e) := fun e he =>
    bc_comap μ _ _ hV _ _ (Hten_le_V lam0 hd _ fun s => hlatL s.val e he)
      (bc_Hten φ φK hφ hinj hinj' lam0 hd _ _ (fun s => hlatL s.val e he)
        fun s => bc_LeAt ι σ φ φK hφ p w s.val e)
  obtain ⟨I0, hI0, b0, -⟩ := jm_HL_basis (mkG hS m r lam0 hd) (0 : Fin 1) L hL
  have : Module.Finite Kf (Vsp Kf lam0) := Module.Finite.of_basis b0
  have hdim : dimV Kf' lam0 = dimV Kf lam0 :=
    (jr_dim (mkG hS' m r lam0 hd) (0 : Fin 1)).symm.trans (jr_dim (mkG hS m r lam0 hd) (0 : Fin 1))
  have hcard : Fintype.card (Fin (Module.finrank Kf (Vsp Kf lam0))) = Module.finrank Kf' (Vsp Kf' lam0) := by
    rw [Fintype.card_fin]; exact hdim.symm
  set x := Module.finBasis Kf (Vsp Kf lam0) with hxdef
  set x' := basisOfTopLeSpanOfCardEqFinrank (fun i => ν (x i)) (span_muV_top μ _ _ hV bV x) hcard with hx'def
  have hx : ∀ i, x' i = ν (x i) := fun i =>
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank (fun i => ν (x i)) (span_muV_top μ _ _ hV bV x) hcard) i
  set δ := deltaS φK x x' with hδ
  have hwz : ∀ z : ℤ, φK (algebraMap O Kf w ^ z) = algebraMap O' Kf' (φ w) ^ z := fun z => by
    rw [map_zpow₀, hφ]
  have hRe : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → ∀ y ∈ Re (O := O) p ι σ w r lam0 e,
      ν y ∈ Re (O := O') p (φK.comp ι) σ (φ w) r lam0 e := by
    intro e he y hy
    have h1 := scale_mem φK ν (fun y hy => (hHLe e he).mem hy) _ hy
    rw [hwz] at h1
    exact h1
  have hRe' : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → ∀ G ∈ Re' (O := O) p ι σ w r lam0 e,
      δ G ∈ Re' (O := O') p (φK.comp ι) σ (φ w) r lam0 e := by
    intro e he G hG
    have h1 := scale_mem φK δ (fun G hG => dual_mem φ φK hφ ν x x' hx _ _ (hHLe e he) G hG) _ hG
    rw [hwz] at h1
    exact h1
  have hN : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A → ∀ y ∈ Nsrc (O := O) p n' ι σ w r lam0 t A,
      ν y ∈ Nsrc (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t A := by
    intro A hA y hy
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := scale_mem φK ν (fun y hy => (hHL A hA).mem hy) _ (Submodule.mem_inf.1 hy).1
      rw [hwz] at h1
      exact h1
    · rw [Submodule.mem_iInf]
      intro e
      rw [Submodule.mem_iInf]
      intro he
      exact hRe e he.1 y ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hy).2 e) he)
  have hN' : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A → ∀ G ∈ Ntgt (O := O) p n' ι σ w r lam0 t A,
      δ G ∈ Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t A := by
    intro A hA G hG
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := scale_mem φK δ (fun G hG => dual_mem φ φK hφ ν x x' hx _ _ (hHL A hA) G hG) _
        (Submodule.mem_inf.1 hG).1
      rw [hwz] at h1
      exact h1
    · rw [Submodule.mem_iInf]
      intro e
      rw [Submodule.mem_iInf]
      intro he
      exact hRe' e he.1 G ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hG).2 e) he)
  obtain ⟨M, e, F, h1, h2, h3, n, hn, u, Mat, hu⟩ := h
  refine ⟨M, e, fun i => ν (F i), h1, fun i => hN _ (h1 i).1.1 _ (h2 i), ?_, n, ?_, ?_⟩
  · intro i e' he' hs hne
    have h4 := scale_mem φK ν (hRe e' he') _ (h3 i e' he' hs hne)
    rw [hwz] at h4
    exact h4
  · rw [hdim]; exact hn
  · have hbe : ∀ (i : Fin M) (Gd : Module.Dual Kf (Vsp Kf lam0)),
        be p r lam0 (ν (F i)) (δ Gd) = φK (be p r lam0 (F i) Gd) := by
      intro i Gd
      unfold be
      have h5 : ((p : Kf') ^ Ar r lam0) • ν (F i) = ν (((p : Kf) ^ Ar r lam0) • F i) := by
        rw [map_smulₛₗ, map_zpow₀, map_natCast]
      rw [h5]
      exact deltaS_apply φK ν x x' hx Gd _
    refine ⟨Fintype.linearCombination O' (fun l : Fin n =>
      (⟨δ (u (Pi.single l 1)).1, hN' L hL _ (u (Pi.single l 1)).2⟩ :
        ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L))), Mat.map φ, ?_⟩
    intro y jj
    have e1 : ∀ i : Fin M, be p r lam0 (ν (F i)) ((Fintype.linearCombination O' (fun l : Fin n =>
        (⟨δ (u (Pi.single l 1)).1, hN' L hL _ (u (Pi.single l 1)).2⟩ :
          ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L))) y :
          ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L)) : Module.Dual Kf' (Vsp Kf' lam0)) =
        ∑ l, algebraMap O' Kf' (y l) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) := by
      intro i
      rw [Fintype.linearCombination_apply, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [be_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hbe]
    have e2 : ∀ l : Fin n, ∑ i, algebraMap O' Kf' (φ (Mat jj i)) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) =
        algebraMap O' Kf' (φ ((p : O) ^ D * (Pi.single l (1 : O) : Fin n → O) jj)) := by
      intro l
      rw [← hφ, ← hu (Pi.single l 1) jj, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hφ]
    simp only [e1, Matrix.map_apply]
    calc ∑ i, algebraMap O' Kf' (φ (Mat jj i)) *
          ∑ l, algebraMap O' Kf' (y l) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1)
        = ∑ l, algebraMap O' Kf' (y l) *
          ∑ i, algebraMap O' Kf' (φ (Mat jj i)) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ l, algebraMap O' Kf' (y l) *
          algebraMap O' Kf' (φ ((p : O) ^ D * (Pi.single l (1 : O) : Fin n → O) jj)) := by
          simp only [e2]
      _ = algebraMap O' Kf' ((p : O') ^ D * y jj) := by
          rw [Finset.sum_eq_single jj]
          · rw [Pi.single_eq_same, mul_one, map_pow, map_natCast, ← map_mul, mul_comm]
          · intro l _ hl
            rw [Pi.single_eq_of_ne hl.symm, mul_zero, map_zero, map_zero, mul_zero]
          · intro hjj
            exact absurd (Finset.mem_univ jj) hjj

end Main

theorem lpBaseChange : Formalism.MainNotions.G.LPBaseChange := by
  intro p n' W Qq O Kf O' Kf' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι σ j w φ φK hφ _ hS hS' m r lam0 t D κ cStar h
  refine ⟨h.1, fun L hL => ?_⟩
  by_cases hd : IsDominant lam0
  · exact lpAt_dom hφ hS hS' m r lam0 hd t D κ cStar L hL (h.2 L hL)
  · exact lpAt_nondom m r lam0 hd t D κ cStar L

end Formalism.L2.G.Model
