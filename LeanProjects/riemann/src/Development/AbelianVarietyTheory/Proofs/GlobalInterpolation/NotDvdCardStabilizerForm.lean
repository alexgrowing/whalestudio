import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

def pairStab {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) (p : Y.Pts) : Subgroup S.G :=
  MulAction.stabilizer S.G p

theorem pairStab_le {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) (p : Y.Pts) {g : S.G}
    (hg : g ∈ pairStab Y p) : g • p.1.1 = p.1.1 :=
  congrArg (fun q : Y.Pts => q.1.1) (show g • p = p from hg)

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

theorem prime_le_and_lt (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) {n : ℕ} (hn : n ≤ R.N R.m)
    (Γ : Subgroup (UF F.E n)) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u := by
  refine ⟨?_, hS.T_big u⟩
  have h := prime_le_of_embed ((UF F.E n).subtype.comp Γ.subtype)
    (Subtype.val_injective.comp Subtype.val_injective) hp hd
  rw [hF.finrank_E] at h
  exact h.trans (Nat.succ_le_succ (Nat.mul_le_mul_left _ hn))

theorem prime_le_and_lt_step (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) {j : ℕ} (hj : j ≤ R.m)
    (Γ : Subgroup (UF F.E (R.N j))) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u :=
  prime_le_and_lt hF hS u (rank_le R hj) Γ hp hd

theorem prime_le_and_lt_row (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word)
    (Γ : Subgroup (UF F.E (R.N R.m - 1))) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u :=
  prime_le_and_lt hF hS u (Nat.sub_le _ _) Γ hp hd

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

theorem exists_embed_deco (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    ∃ φ : G →* MulAction.stabilizer (UF F.E n × GLG F.E n SG) p.deco, Function.Injective φ :=
  ⟨{ toFun := fun g => ⟨((j g).1, ((j g).2.1 : GLG F.E n SG)), congrArg DecoF.deco (hfix g)⟩
     map_one' := Subtype.ext (by
       show (((j 1).1, ((j 1).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = 1
       rw [map_one]; rfl)
     map_mul' := fun x y => Subtype.ext (by
       show (((j (x * y)).1, ((j (x * y)).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = _
       rw [map_mul]; rfl) }, fun x y h => by
    have h1 : (((j x).1, ((j x).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = ((j y).1, ((j y).2.1 : GLG F.E n SG)) :=
      congrArg Subtype.val h
    exact hj (FramedForms.incl_injective Λ Θ
      (FramedForms.stab_inj p (hfix x) (hfix y) (Prod.mk.inj h1).1 (Prod.mk.inj h1).2))⟩

theorem finite_and_prime_le_frm (hF : F.Ok) (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    Finite G ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q ≤ 2 * F.f * n + 1 := by
  obtain ⟨φ, hφ⟩ := exists_embed_deco Λ Θ p j hj hfix
  haveI := DecoSet.finite_stabilizer (posStar_of_conj hF.conjE) p.deco
  refine ⟨Finite.of_injective φ hφ, fun q hq hd => ?_⟩
  have h := DecoSet.prime_le_of_dvd_card p.deco _ le_rfl hq (hd.trans (Subgroup.card_dvd_of_injective φ hφ))
  rwa [hF.finrank_E] at h

theorem not_dvd_card_frm (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    ¬ Pr.T u ∣ Nat.card G := fun hd => by
  have h1 := (finite_and_prime_le_frm hF Λ Θ p j hj hfix).2 _ hT hd
  have h2 := hS.T_big u
  have h3 := Nat.mul_le_mul_left (2 * F.f) hn
  omega

theorem not_dvd_card_stabilizer_over (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) {G Z : Type} [Group G] [MulAction G Z]
    (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (π : Z → DecoF F.E n ST SG Q) (hπ : ∀ g z, π (g • z) = j g • π z) (z : Z) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer G z) :=
  not_dvd_card_frm hF hS u hT hn Λ Θ (π z) (j.comp (MulAction.stabilizer G z).subtype) (hj.comp Subtype.val_injective)
    fun g => (hπ g.1 z).symm.trans (congrArg π g.2)

theorem not_dvd_card_stabilizer_form (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (d : DecoSet F.E n ST SG) : ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer (FormG Λ) d) := fun hd => by
  haveI := DecoSet.finite_stabilizer (posStar_of_conj hF.conjE) d
  let φ : MulAction.stabilizer (FormG Λ) d →* MulAction.stabilizer (UF F.E n × GLG F.E n SG) d :=
    { toFun := fun g => ⟨FormG.incl Λ g.1, g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h => by
    have h1 : FormG.incl Λ x.1 = FormG.incl Λ y.1 := congrArg Subtype.val h
    have h2 := congrArg Prod.fst h1
    have h3 := congrArg Prod.snd h1
    exact Subtype.ext (Prod.ext h2 (Subtype.ext h3))
  have h1 := DecoSet.prime_le_of_dvd_card d _ le_rfl hT (hd.trans (Subgroup.card_dvd_of_injective φ hφ))
  rw [hF.finrank_E] at h1
  have h2 := hS.T_big u
  have h3 := Nat.mul_le_mul_left (2 * F.f) hn
  omega

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

theorem not_dvd_card_chF (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) (p : ((chF W sel mu L u j).mem b).D) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer ((chF W sel mu L u j).mem b).G p) :=
  not_dvd_card_stabilizer_over hF hS u hT (rank_le R hj) (L.levG j b) (L.levQ j b) (G := ((chF W sel mu L u j).mem b).G)
    (MonoidHom.id _) Function.injective_id id (fun _ _ => rfl) p

theorem not_dvd_card_cpl (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) {m2 : ℕ} (hm : m2 + 1 ≤ R.m)
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (p : (ybCpl W sel mu cst L u m2 b hY).Pts) :
    ¬ Pr.T u ∣ Nat.card (pairStab (ybCpl W sel mu cst L u m2 b hY) p) :=
  not_dvd_card_frm hF hS u hT (rank_le R hm) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) p.1.1
    (pairStab (ybCpl W sel mu cst L u m2 b hY) p).subtype Subtype.val_injective fun g => pairStab_le _ p g.2

theorem not_dvd_card_evGSD (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (Cr : Chars F Pr R.m)
    (P : LevFam F.E F.K R.r Pr.vGs) (d : (evGSD W Cr sel mu P u).D) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer (evGSD W Cr sel mu P u).G d) :=
  not_dvd_card_stabilizer_form hF hS u hT (Nat.sub_le _ _) _ d

theorem not_dvd_card_stepAt (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime)
    (Tp : TopLev F Pr R (QE sel (mu : Chr F.F F.E F.K))) {j : ℕ} (hj : j ≤ R.m) (c : (stepAt sel mu cst L Tp u j).Cl) :
    ¬ Pr.T u ∣ Nat.card ((stepAt sel mu cst L Tp u j).Stab c) :=
  letI := (stepAt sel mu cst L Tp u j).actD c.1
  not_dvd_card_stabilizer_over hF hS u hT (rank_le R hj) (levGAt sel mu L Tp j c.1) (levQAt sel mu L Tp j c.1)
    (G := (stepAt sel mu cst L Tp u j).G c.1) (Z := (stepAt sel mu cst L Tp u j).D c.1)
    (MonoidHom.id _) Function.injective_id (fun p => p.1.1) (fun _ _ => rfl) _

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

theorem not_dvd_card_stabP {X : Ch D u} (h : StabUnit X) (c : X.fm.clsP) : ¬ X.A.T ∣ Nat.card (X.fm.stabilizer₂ c) := fun hd =>
  h _ le_rfl (X.fm.til c) (hd.trans (Subgroup.card_dvd_of_injective (X.fm.stabMap c) (X.fm.stabMap_inj c)))

theorem stabUnit_of_concrete (X : Ch D u) {F : Fields} (hF : F.Ok) {Pr : Primes F} (W : Wts F Pr.Word D.R) {a : ℝ}
    (hS : Sizes Pr W a) (u' : Pr.Word) (hT : Pr.T u' = X.A.T)
    (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
    (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr D.R (QE sel (mu : Chr F.F F.E F.K)))
    (m2 : ℕ) (hm : D.R.m = m2 + 2) (b : L.β (m2 + 1)) (hY : YbHyp (R := D.R) sel mu cst L u' m2 b)
    (Λ : LevFam F.E F.K (D.R.N D.R.m) Pr.vGs) (Θ : LevQFam F.E F.K (D.R.N D.R.m) (QE sel (mu : Chr F.F F.E F.K)))
    (hlow : ∀ i, i ≤ m2 → ∀ c : X.C.cls i, ∃ (β : L.β i) (p : ((chF W sel mu L u' i).mem β).D),
      Nonempty (X.C.stab i c ≃* MulAction.stabilizer ((chF W sel mu L u' i).mem β).G p))
    (hmid : ∀ c : X.C.cls (m2 + 1), ∃ p : (ybCpl W sel mu cst L u' m2 b hY).Pts,
      Nonempty (X.C.stab (m2 + 1) c ≃* pairStab (ybCpl W sel mu cst L u' m2 b hY) p))
    (htop : ∀ c : X.C.cls D.R.m, ∃ p : (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).D,
      Nonempty (X.C.stab D.R.m c ≃* MulAction.stabilizer (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).G p)) :
    StabUnit X := by
  have hp : (Pr.T u').Prime := hT ▸ X.A.T_prime
  intro i hi c
  rw [← hT]
  rcases (show i ≤ m2 ∨ i = m2 + 1 ∨ i = D.R.m by omega) with h | rfl | rfl
  · obtain ⟨β, p, ⟨e⟩⟩ := hlow i h c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_chF sel mu L hF hS u' hp hi β p
  · obtain ⟨p, ⟨e⟩⟩ := hmid c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_cpl sel mu cst L hF hS u' hp hi b hY p
  · obtain ⟨p, ⟨e⟩⟩ := htop c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_stabilizer_over hF hS u' hp le_rfl Λ Θ (G := (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).G)
      (MonoidHom.id _) Function.injective_id id (fun _ _ => rfl) p

end Record

end GlobalTheory.LvT.StabOrder
