import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumPosHerm

noncomputable section

namespace GlobalTheory.LvT.Built.RealM

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂)

def UG (E : Type) [Field E] [StarRing E] (n : ℕ) : Subgroup (GL (Fin n) E) where
  carrier := {γ | (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, conjTranspose_mul] at *
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (a : Matrix (Fin n) (Fin n) E), ha, Matrix.one_mul, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (a : Matrix (Fin n) (Fin n) E)ᴴ := by
      rw [← Matrix.one_mul ((a⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E), ← ha, Matrix.mul_assoc, Units.mul_inv,
        Matrix.mul_one]
    rw [h1, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 ha

abbrev GG (E K : Type) [Field E] [StarRing E] [Field K] (n : ℕ) : Type := UG E n × CommGroup.torsion Kˣ

section Val

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem trFr_mem (γ : GL (Fin n) E) (c : Kˣ) {f : Fr emb σ n → ℂ} (hf : f ∈ ValC (Gr emb σ n) lam) :
    trFr emb σ γ c f ∈ ValC (Gr emb σ n) lam := by
  obtain ⟨F, rfl⟩ := (GlobalTheory.TilClass.mem_ValC_iff emb σ _ _).1 hf
  rw [GlobalTheory.TilClass.trFr_fnOf]
  exact Submodule.smul_mem _ _ ((GlobalTheory.TilClass.mem_ValC_iff emb σ _ _).2 ⟨_, rfl⟩)

def actV : GG E K n →* Module.End ℂ (ValC (Gr emb σ n) lam) where
  toFun h := (trFr emb σ h.1.1 h.2.1).toLinearMap.restrict fun _ hf => trFr_mem emb σ lam _ _ hf
  map_one' := by
    ext y x
    show trFr emb σ 1 1 y.1 x = y.1 x
    simp [trFr_apply, frMul_one]
  map_mul' a b := by
    ext y x
    show trFr emb σ (a.1.1 * b.1.1) (a.2.1 * b.2.1) y.1 x = trFr emb σ a.1.1 a.2.1 (trFr emb σ b.1.1 b.2.1 y.1) x
    simp only [trFr_apply, map_mul, _root_.mul_inv_rev, frMul_mul, Units.val_mul, mul_assoc]

theorem ipVal_trFr (hF : FOk emb σ) (h : GG E K n) {f f' : Fr emb σ n → ℂ} (hf : f ∈ ValC (Gr emb σ n) lam)
    (hf' : f' ∈ ValC (Gr emb σ n) lam) :
    ipVal emb σ lam (trFr emb σ h.1.1 h.2.1 f) (trFr emb σ h.1.1 h.2.1 f') = ipVal emb σ lam f f' := by
  obtain ⟨⟨γ, hγ⟩, ⟨c, hc⟩⟩ := h
  obtain ⟨P, -, rfl⟩ := hf
  obtain ⟨Q, -, rfl⟩ := hf'
  have hG : ∀ τ, Gr emb σ n τ = 1 := fun τ => by simp [gramC]
  have e0 : (1 : ι → Matrix (Fin n) (Fin n) ℂ) = fun τ => ((fr0 emb σ n).1 τ)⁻¹ := funext fun τ => inv_one.symm
  have h0 : ∀ τ, ((fr0 emb σ n).1 τ)ᴴ * Gr emb σ n τ * (fr0 emb σ n).1 τ = 1 := fun τ => by
    rw [hG]; show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 * 1 = 1; simp
  let o := frMul emb σ γ (fr0 emb σ n)
  have ho : ∀ τ, o.1 τ = (γ : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) := fun τ => Matrix.mul_one _
  have h1 : ∀ τ, (o.1 τ)ᴴ * Gr emb σ n τ * o.1 τ = 1 := fun τ => by
    rw [hG, ho, Matrix.mul_one, ← Matrix.conjTranspose_map _ (fun x => hF.conjE _ x), ← Matrix.map_mul,
      show (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1 from hγ]
    simp
  have hi : ∀ τ, (o.1 τ)⁻¹ = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) := fun τ => by
    rw [ho]
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Units.inv_mul]
    simp
  have ht : ∀ P, trFr emb σ γ c (fnOf (Gr emb σ n) (shiftOf lam) 1 P) =
      σ c • fnOf (Gr emb σ n) (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P := fun P => by
    funext y
    rw [trFr_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [hi, fnOf, LinearMap.coe_mk, AddHom.coe_mk, frMul, Pi.one_apply, Matrix.one_mul]
  have hn : starRingEnd ℂ (σ c) * σ c = 1 := by
    obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have e1 : (σ c) ^ m = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, e]; simp
    have e2 : ‖σ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one e1 hm.ne'
    rw [Complex.conj_mul', e2]; simp
  show ipVal emb σ lam (trFr emb σ γ c _) (trFr emb σ γ c _) = _
  rw [ht, ht, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_smul, mul_comm, hn, one_smul]
  unfold ipVal
  rw [ipFr_fnOf _ _ _ _ h0 h1, e0, ipFr_fnOf _ _ _ _ h0 h0]

def ipV : ValC (Gr emb σ n) lam →ₗ⋆[ℂ] ValC (Gr emb σ n) lam →ₗ[ℂ] ℂ :=
  ((ipVal emb σ lam).comp (ValC (Gr emb σ n) lam).subtype).compl₂ (ValC (Gr emb σ n) lam).subtype

end Val

section Pts

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

structure Hyp (A : TDat S ST) (T : ℕ) : Prop where
  s : S.Ok
  a : A.Ok T
  t : A.Tied T

theorem tAt (sp : Split A T) : TAt T ST :=
  ⟨fun P => ⟨sp.T_mem P P.2, sp.T_nsq P P.2⟩, fun P Q => sp.nonconj P P.2 Q Q.2⟩

def chrT (h : Hyp A T) (b : S.β) : S.G b →* CommGroup.torsion Kˣ :=
  (S.chr b).codRestrict _ fun g => isOfFinOrder_iff_pow_eq_one.2 (h.s.root b g)

def phi (h : Hyp A T) (b : S.β) : S.G b →* GG E K n :=
  ((S.gam b).codRestrict (UG E n) fun g => h.s.unit b g).prod (chrT h b)

def rel (h : Hyp A T) (sp : Split A T) (b : S.β) : Setoid (CommGroup.torsion Kˣ × S.D b) where
  r x y := ∃ g : S.G b, S.gam b g = 1 ∧ x.1 = y.1 * chrT h b g ∧ (sp.off b).r (g • x.2) y.2
  iseqv := by
    refine ⟨fun x => ⟨1, by simp, by simp, by rw [one_smul]⟩, ?_, ?_⟩
    · rintro x y ⟨g, h1, h2, h3⟩
      refine ⟨g⁻¹, by rw [map_inv, h1, inv_one], by rw [h2, map_inv, mul_inv_cancel_right], ?_⟩
      have := sp.off_act b g⁻¹ _ _ h3
      rw [inv_smul_smul] at this
      exact (sp.off b).symm this
    · rintro x y z ⟨g, h1, h2, h3⟩ ⟨g', h1', h2', h3'⟩
      refine ⟨g' * g, by rw [map_mul, h1, h1', one_mul], by rw [h2, h2', map_mul, mul_assoc], ?_⟩
      rw [mul_smul]
      exact (sp.off b).trans (sp.off_act b g' _ _ h3) h3'

def ZZ (h : Hyp A T) (sp : Split A T) : Type := Σ b, Quotient (rel h sp b)

def prs (h : Hyp A T) (sp : Split A T) (b : S.β) (d : S.D b) (P : ST) : LocF.PP (locF ((tAt sp).unif P)) n :=
  pair ((tAt sp).unif P) (A.deco b d) (h.t.ok b d)

abbrev PT (h : Hyp A T) (sp : Split A T) : Type := ZZ h sp × ∀ P : ST, LocF.PP (locF ((tAt sp).unif P)) n

def mk (h : Hyp A T) (sp : Split A T) (b : S.β) (ζ : CommGroup.torsion Kˣ) (d : S.D b) : PT h sp :=
  (⟨b, Quotient.mk _ (ζ, d)⟩, prs h sp b d)

variable (h : Hyp A T) (sp : Split A T)

theorem mk_fst_iff (b : S.β) (ζ ζ' : CommGroup.torsion Kˣ) (d d' : S.D b) :
    (mk h sp b ζ d).1 = (mk h sp b ζ' d').1 ↔
      ∃ g : S.G b, S.gam b g = 1 ∧ ζ = ζ' * chrT h b g ∧ (sp.off b).r (g • d) d' :=
  ⟨fun e => Quotient.exact (eq_of_heq (Sigma.mk.inj e).2), fun e => congrArg (Sigma.mk b) (Quotient.sound e)⟩

theorem prs_act (b : S.β) (g : S.G b) (d : S.D b) (P : ST) :
    LocF.PP.IsAct (S.gam b g) (prs h sp b d P) (prs h sp b (g • d) P) := by
  intro x
  refine ⟨?_, h.a.f_act b g d P x⟩
  show _ ∈ localization₂ P.1.asIdeal (A.N b (g • d)) ↔ x ∈ localization₂ P.1.asIdeal (A.N b d)
  rw [memLoc, memLoc]
  refine exists_congr fun s => and_congr Iff.rfl ?_
  rw [← h.a.N_act b g d, Matrix.mulVec_smul]

theorem prs_triv (b : S.β) (g : S.G b) (hg : S.gam b g = 1) (d : S.D b) : prs h sp b (g • d) = prs h sp b d := by
  funext P
  have := prs_act h sp b g d P
  rw [hg] at this
  refine pp_ext (fun x => ?_) fun x _ => ?_
  · simpa using (this x).1
  · simpa using (this x).2

theorem mk_eq_iff (b : S.β) (ζ ζ' : CommGroup.torsion Kˣ) (d d' : S.D b) :
    mk h sp b ζ d = mk h sp b ζ' d' ↔ ∃ g : S.G b, S.gam b g = 1 ∧ ζ = ζ' * chrT h b g ∧ g • d = d' := by
  constructor
  · intro e
    obtain ⟨g, h1, h2, h3⟩ := (mk_fst_iff h sp b ζ ζ' d d').1 (congrArg Prod.fst e)
    refine ⟨g, h1, h2, sp.ext b _ _ h3 ?_⟩
    refine deco_ext (tAt sp) (h.t.ok _ _) (h.t.ok _ _) (fun w hw => sp.off_lat b _ _ h3 w fun P hP => hw ⟨P, hP⟩) fun P => ?_
    exact congrFun ((prs_triv h sp b g h1 d).trans (congrArg Prod.snd e)) P
  · rintro ⟨g, h1, h2, rfl⟩
    exact Prod.ext ((mk_fst_iff h sp b ζ ζ' d _).2 ⟨g, h1, h2, (sp.off b).refl _⟩) (prs_triv h sp b g h1 d).symm

theorem mk_surj (p : PT h sp) : ∃ x : Σ b, CommGroup.torsion Kˣ × S.D b, mk h sp x.1 x.2.1 x.2.2 = p := by
  obtain ⟨⟨b, q⟩, p⟩ := p
  obtain ⟨⟨ζ, d⟩, rfl⟩ := Quotient.exists_rep q
  obtain ⟨e, he, ho, hp⟩ := exists_deco (tAt sp) (h.t.ok b d).lat (h.t.ok b d).uni p
  obtain ⟨d', h1, h2⟩ := sp.surj b d e he fun w hw => ho w fun P => hw P.1 P.2
  subst h2
  refine ⟨⟨b, ζ, d'⟩, Prod.ext ?_ (funext hp)⟩
  exact (mk_fst_iff h sp b ζ ζ d' d).2 ⟨1, by simp, by simp, by rw [one_smul]; exact (sp.off b).symm h1⟩

def lift (b : S.β) (γ : UG E n) : S.G b := (sp.gam_surj b γ.1 γ.2).choose

theorem gam_lift (b : S.β) (γ : UG E n) : S.gam b (lift sp b γ) = γ.1 := (sp.gam_surj b γ.1 γ.2).choose_spec

def sm (k : GG E K n) (p : PT h sp) : PT h sp :=
  let x := (mk_surj h sp p).choose
  mk h sp x.1 (k.2 * x.2.1 * (chrT h x.1 (lift sp x.1 k.1))⁻¹) (lift sp x.1 k.1 • x.2.2)

theorem sm_mk (k : GG E K n) (b : S.β) (ζ : CommGroup.torsion Kˣ) (d : S.D b) (g : S.G b) (hg : S.gam b g = k.1.1) :
    sm h sp k (mk h sp b ζ d) = mk h sp b (k.2 * ζ * (chrT h b g)⁻¹) (g • d) := by
  unfold sm
  have hx := (mk_surj h sp (mk h sp b ζ d)).choose_spec
  generalize (mk_surj h sp (mk h sp b ζ d)).choose = x at hx
  obtain ⟨b', ζ', d'⟩ := x
  obtain rfl : b' = b := congrArg (fun p : PT h sp => p.1.1) hx
  obtain ⟨g0, h1, h2, rfl⟩ := (mk_eq_iff h sp _ _ _ _ _).1 hx
  refine (mk_eq_iff h sp _ _ _ _ _).2 ⟨g * g0 * (lift sp b' k.1)⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, gam_lift, hg, h1, mul_one, mul_inv_cancel]
  · dsimp only at h2 ⊢
    rw [h2, map_mul, map_mul, map_inv]
    simp only [mul_assoc, inv_mul_cancel_left]
  · rw [mul_smul, mul_smul, inv_smul_smul]

instance actPT : MulAction (GG E K n) (PT h sp) where
  smul := sm h sp
  one_smul p := by
    obtain ⟨⟨b, ζ, d⟩, rfl⟩ := mk_surj h sp p
    show sm h sp 1 _ = _
    rw [sm_mk h sp 1 b ζ d 1 (map_one _)]
    simp
  mul_smul k k' p := by
    obtain ⟨⟨b, ζ, d⟩, rfl⟩ := mk_surj h sp p
    show sm h sp _ _ = sm h sp _ (sm h sp _ _)
    rw [sm_mk h sp k' b ζ d _ (gam_lift sp b _), sm_mk h sp k b _ _ _ (gam_lift sp b _),
      sm_mk h sp (k * k') b ζ d (lift sp b k.1 * lift sp b k'.1) (by rw [map_mul, gam_lift, gam_lift]; rfl), mul_smul]
    congr 1
    rw [map_mul, Prod.snd_mul, _root_.mul_inv_rev]
    simp only [mul_assoc]

theorem smul_mk (k : GG E K n) (b : S.β) (ζ : CommGroup.torsion Kˣ) (d : S.D b) (g : S.G b) (hg : S.gam b g = k.1.1) :
    k • mk h sp b ζ d = mk h sp b (k.2 * ζ * (chrT h b g)⁻¹) (g • d) := sm_mk h sp k b ζ d g hg

theorem phi_smul (b : S.β) (g : S.G b) (d : S.D b) : phi h b g • mk h sp b 1 d = mk h sp b 1 (g • d) := by
  rw [smul_mk h sp _ b 1 d g rfl]
  congr 1
  show chrT h b g * 1 * _ = 1
  simp

theorem inr_smul (ζ : CommGroup.torsion Kˣ) (b : S.β) (d : S.D b) :
    (MonoidHom.inr (UG E n) (CommGroup.torsion Kˣ) ζ : GG E K n) • mk h sp b 1 d = mk h sp b ζ d := by
  rw [smul_mk h sp _ b 1 d 1 (map_one _)]
  simp

theorem smul_eq_iff (k : GG E K n) (b : S.β) (d d' : S.D b) :
    k • mk h sp b 1 d = mk h sp b 1 d' ↔ ∃ g, phi h b g = k ∧ g • d = d' := by
  constructor
  · intro e
    rw [smul_mk h sp k b 1 d _ (gam_lift sp b _), mk_eq_iff] at e
    obtain ⟨g, h1, h2, h3⟩ := e
    refine ⟨g * lift sp b k.1, Prod.ext (Subtype.ext ?_) ?_, by rw [mul_smul, h3]⟩
    · show S.gam b _ = _
      rw [map_mul, h1, one_mul, gam_lift]
    · show chrT h b _ = _
      rw [mul_one, one_mul, mul_inv_eq_iff_eq_mul] at h2
      rw [map_mul, h2]
  · rintro ⟨g, rfl, rfl⟩
    exact phi_smul h sp b g d

theorem smul_fst (k : GG E K n) (p p' : PT h sp) (e : p.1 = p'.1) : (k • p).1 = (k • p').1 := by
  obtain ⟨⟨b, ζ, d⟩, rfl⟩ := mk_surj h sp p
  obtain ⟨⟨b', ζ', d'⟩, rfl⟩ := mk_surj h sp p'
  obtain rfl : b = b' := congrArg Sigma.fst e
  obtain ⟨g0, h1, h2, h3⟩ := (mk_fst_iff h sp _ _ _ _ _).1 e
  rw [smul_mk h sp k b ζ d _ (gam_lift sp b _), smul_mk h sp k b ζ' d' _ (gam_lift sp b _), mk_fst_iff]
  refine ⟨lift sp b k.1 * g0 * (lift sp b k.1)⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  · dsimp only at h2 ⊢
    rw [h2, map_mul, map_mul, map_inv]
    simp only [mul_assoc, inv_mul_cancel_left]
  · rw [mul_smul, mul_smul, inv_smul_smul]
    exact sp.off_act b _ _ _ h3

theorem smul_snd (k : GG E K n) (p : PT h sp) (P : ST) : LocF.PP.IsAct k.1.1 (p.2 P) ((k • p).2 P) := by
  obtain ⟨⟨b, ζ, d⟩, rfl⟩ := mk_surj h sp p
  rw [smul_mk h sp k b ζ d _ (gam_lift sp b _), ← gam_lift sp b k.1]
  exact prs_act h sp b _ d P

theorem rep_surj (p : PT h sp) : ∃ (c : S.Cl) (k : GG E K n), k • mk h sp c.1 1 (S.rep c) = p := by
  obtain ⟨⟨b, ζ, d⟩, rfl⟩ := mk_surj h sp p
  refine ⟨S.cl b d, MonoidHom.inr (UG E n) (CommGroup.torsion Kˣ) ζ * phi h b (S.mv b d), ?_⟩
  rw [mul_smul, phi_smul, S.mv_smul, inr_smul]

theorem rep_inj (c c' : S.Cl) (k : GG E K n) (e : k • mk h sp c.1 1 (S.rep c) = mk h sp c'.1 1 (S.rep c')) : c = c' := by
  obtain ⟨b, q⟩ := c
  obtain ⟨b', q'⟩ := c'
  obtain rfl : b = b' := by
    rw [smul_mk h sp k b 1 _ _ (gam_lift sp b _)] at e
    exact congrArg (fun p : PT h sp => p.1.1) e
  obtain ⟨g, -, hg⟩ := (smul_eq_iff h sp k b _ _).1 e
  refine congrArg (Sigma.mk b) ?_
  rw [← S.rp_spec b q, ← S.rp_spec b q']
  exact Quotient.sound ((MulAction.orbitRel (S.G b) (S.D b)).symm ⟨g, hg⟩)

theorem card_stab (b : S.β) (d : S.D b) :
    Nat.card (MulAction.stabilizer (S.G b) d) = Nat.card (MulAction.stabilizer (GG E K n) (mk h sp b 1 d)) := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨phi h b g.1, (smul_eq_iff h sp _ b d d).2 ⟨g.1, rfl, g.2⟩⟩) ⟨?_, ?_⟩)
  · intro g g' e
    have e1 : S.gam b g.1 = S.gam b g'.1 := congrArg (fun k => k.1.1.1) e
    have := h.s.stab_inj b (g⁻¹ * g').1 d (g⁻¹ * g').2 (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, e1, inv_mul_cancel])
    exact inv_mul_eq_one.1 (Subtype.ext this)
  · rintro ⟨k, hk⟩
    obtain ⟨g, rfl, hg⟩ := (smul_eq_iff h sp k b d d).1 hk
    exact ⟨⟨g, hg⟩, rfl⟩

theorem mk_move {inst : DecidableEq ST} (b : S.β) (d d' : S.D b) (P : ST) (p₁ : LocF.PP (locF ((tAt sp).unif P)) n) (ho : (sp.off b).r d d')
    (h1 : prs h sp b d' P = p₁) (h2 : ∀ Q, Q ≠ P → prs h sp b d' Q = prs h sp b d Q) :
    phi h b (S.mv b d') • mk h sp b 1 (S.rep (S.cl b d')) =
      ((mk h sp b 1 d).1, Function.update (mk h sp b 1 d).2 P p₁) := by
  rw [phi_smul, S.mv_smul]
  refine Prod.ext ((mk_fst_iff h sp b 1 1 d' d).2 ⟨1, by simp, by simp, by rw [one_smul]; exact (sp.off b).symm ho⟩) ?_
  funext Q
  dsimp only
  by_cases e : Q = P
  · subst e
    rw [Function.update_self]
    exact h1
  · rw [Function.update_of_ne e]
    exact h2 Q e

include h in
theorem fv_redL (hl : A.Laws T) (P : ST) (c : S.Cl) {x : Fin n → E} (hx : x ∈ localization₂ P.1.asIdeal (A.N c.1 (S.rep c))) :
    A.fv P c (redL _ P.1 x) = A.f c.1 (S.rep c) P x := by
  refine dual_redL ((h.t.ok c.1 (S.rep c)).f_smul P) _ ?_ hx
  have h0 := hl.fv_ne P c
  unfold TDat.fv at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact h1.choose_spec
  · exact absurd rfl h0

theorem mem_ker (b : S.β) (d : S.D b) (P : ST) (x : Fin n → E) :
    x ∈ (prs h sp b d P).ker ↔ x ∈ localization₂ P.1.asIdeal (A.dnN b d P) := by
  rw [h.t.dnN_eq]
  exact mem_pair_ker _ ((tAt sp).ne P) _ x

include h sp in
theorem redL_te (hl : A.Laws T) (P : ST) (c : S.Cl) (e : Fin n → E) (he : A.f c.1 (S.rep c) P e = 1) :
    redL (A.dnN c.1 (S.rep c) P) P.1 ((T : E) • e) = A.te T P c := by
  have h0 := hl.te_ne P c
  unfold TDat.te at h0 ⊢
  split_ifs at h0 ⊢ with h1
  swap
  · exact absurd rfl h0
  obtain ⟨e', he', hf, ht⟩ := h1.choose_spec
  generalize h1.choose = t at ht
  let p := prs h sp c.1 (S.rep c) P
  have m1 : e ∈ p.1.L := mem_of_f_ne p (by show A.f c.1 (S.rep c) P e ≠ 0; rw [he]; exact one_ne_zero)
  have m2 : e' ∈ p.1.L := le_locP P.1 _ he'
  have m3 : e + (-1 : GlobalTheory.LvT.Inh.valO P.1) • e' ∈ p.ker := ⟨p.1.L.add_mem m1 (p.1.L.smul_mem _ m2), by
    rw [p.2.add _ m1 _ (p.1.L.smul_mem _ m2), p.2.smul _ _ m2, map_neg, map_one]
    show A.f c.1 (S.rep c) P e + -1 * A.f c.1 (S.rep c) P e' = 0
    rw [he, hf]; ring⟩
  rw [mem_ker] at m3
  have e1 : (T : E) • e = toO P.1 T • (e + (-1 : GlobalTheory.LvT.Inh.valO P.1) • e') + (t : Fin n → E) := by
    rw [ht, toO_smul, neg_one_smul, ← smul_add, neg_add_cancel_right, ← algebraMap_smul E (T : 𝓞 E), map_natCast]
  rw [e1, redL_add ((locO P.1 _).smul_mem _ m3) (le_locP P.1 _ t.2), redL_smul _ m3, resP_toO,
    Ideal.Quotient.eq_zero_iff_mem.2 (sp.T_mem P P.2), zero_smul, zero_add, redL_coe]

theorem up_spec (hl : A.Laws T) (P : ST) (c : S.Cl) (x : Fin n → E) (p₁ : LocF.PP (locF ((tAt sp).unif P)) n)
    (hf : A.f c.1 (S.rep c) P x = 1) (hp : (prs h sp c.1 (S.rep c) P).IsUp x p₁) :
    (sp.off c.1).r (S.rep c) (A.upPt P c (redL _ P.1 x)) ∧ prs h sp c.1 (A.upPt P c (redL _ P.1 x)) P = p₁ ∧
      ∀ Q, Q ≠ P → prs h sp c.1 (A.upPt P c (redL _ P.1 x)) Q = prs h sp c.1 (S.rep c) Q := by
  unfold TDat.upPt
  have hr : redL (A.N c.1 (S.rep c)) P.1 ((Quotient.out (redL (A.N c.1 (S.rep c)) P.1 x) : A.N c.1 (S.rep c)) : Fin n → E) =
      redL (A.N c.1 (S.rep c)) P.1 x := by
    rw [redL_coe]; exact Quotient.out_eq _
  generalize (Quotient.out (redL (A.N c.1 (S.rep c)) P.1 x) : A.N c.1 (S.rep c)) = z at hr
  have hz : A.f c.1 (S.rep c) P z = 1 := by
    rw [← fv_redL h hl P c (le_locP P.1 _ z.2), hr, fv_redL h hl P c hp.1, hf]
  have hd := h.t.up_deco c.1 (S.rep c) P z z.2 hz
  have hu := h.t.ok c.1 (A.up c.1 (S.rep c) P z)
  rw [hd] at hu
  refine ⟨sp.off_up _ _ P z z.2 hz, ?_, fun Q hQ => ?_⟩
  · refine Eq.trans ?_ (pair_up (tAt sp) (h.t.ok _ _) P z.2 hz hr hp hu)
    unfold prs
    congr 1
  · refine Eq.trans ?_ (pair_up_ne (tAt sp) (h.t.ok _ _) hQ z.2 hu)
    unfold prs
    congr 1

theorem dn_spec (P : ST) (c : S.Cl) (γ : Module.Dual (Res P.1) (A.lk P c)) (p₀ : LocF.PP (locF ((tAt sp).unif P)) n)
    (hp : (p₀.1.L : Set (Fin n → E)) = (prs h sp c.1 (S.rep c) P).ker)
    (hf : ∀ x ∈ p₀.1.L, p₀.1.f x = γ (redL _ P.1 x)) :
    (sp.off c.1).r (S.rep c) (A.dnPt P c γ) ∧ prs h sp c.1 (A.dnPt P c γ) P = p₀ ∧
      ∀ Q, Q ≠ P → prs h sp c.1 (A.dnPt P c γ) Q = prs h sp c.1 (S.rep c) Q := by
  unfold TDat.dnPt
  have hL : ∀ x, x ∈ localization₂ P.1.asIdeal (A.dnN c.1 (S.rep c) P) ↔ x ∈ p₀.1.L := fun x => by
    rw [← mem_ker h sp, ← hp]; rfl
  have e0 : TDat.extF (A.dnN c.1 (S.rep c) P) P.1 γ = p₀.1.f := by
    funext x
    by_cases hx : x ∈ localization₂ P.1.asIdeal (A.dnN c.1 (S.rep c) P)
    · rw [extF_of_mem γ hx, hf x ((hL x).1 hx)]
    · rw [extF_of_notMem γ hx, p₀.2.off x fun h' => hx ((hL x).2 h')]
  rw [e0]
  have hok := dn_ok (tAt sp) (h.t.ok c.1 (S.rep c)) P p₀ hp
  have hd := h.t.dn_deco c.1 (S.rep c) P _ hok
  refine ⟨sp.off_dn _ _ P _ hok, ?_, fun Q hQ => ?_⟩
  · refine Eq.trans ?_ (pair_dn (tAt sp) (h.t.ok _ _) P p₀ hp hok)
    unfold prs
    congr 1
  · refine Eq.trans ?_ (pair_dn_ne (tAt sp) (h.t.ok _ _) hQ hok)
    unfold prs
    congr 1

theorem dil_spec (P : ST) (c : S.Cl) (a : (Res P.1)ˣ) (p' : LocF.PP (locF ((tAt sp).unif P)) n)
    (hp : LocF.PP.IsDil (a : Res P.1) (prs h sp c.1 (S.rep c) P) p') :
    (sp.off c.1).r (S.rep c) (A.diaPt P a c) ∧ prs h sp c.1 (A.diaPt P a c) P = p' ∧
      ∀ Q, Q ≠ P → prs h sp c.1 (A.diaPt P a c) Q = prs h sp c.1 (S.rep c) Q := by
  unfold TDat.diaPt
  have hN := h.a.dia_N c.1 P a (S.rep c)
  refine ⟨sp.off_dia _ _ P a, pp_ext (fun x => ?_) fun x _ => ?_, fun Q hQ => ?_⟩
  · rw [hp.1]
    show x ∈ localization₂ P.1.asIdeal (A.N _ _) ↔ x ∈ localization₂ P.1.asIdeal (A.N _ _)
    rw [hN]
  · rw [hp.2]
    exact h.a.dia_f c.1 P a _ x
  · exact pair_congr _ _ _ (congrArg (localization₂ Q.1.asIdeal) hN) (sp.dia_deco _ _ P Q a hQ)

end Pts

section Model

variable {D : D7} {u : D.what₂.Word} (B : Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T)

theorem hyp : Hyp (B.J.A i) B.J.T := ⟨B.hI.step i, B.hJ.lev i, B.hJ.tied i⟩

def model : PtModel B.ch i where
  Lc v := locF ((tAt sp).unif (B.pr v))
  G := GG B.E D.what₂.LL (D.R.N i)
  Z := ZZ (hyp B i) sp
  actP := actPT (hyp B i) sp
  loc _ := (UG B.E (D.R.N i)).subtype.comp (MonoidHom.fst _ _)
  smul_fst := smul_fst (hyp B i) sp
  smul_snd := smul_snd (hyp B i) sp
  rep c := mk (hyp B i) sp c.1 1 ((B.I.S i).rep c)
  rep_surj := rep_surj (hyp B i) sp
  rep_inj := rep_inj (hyp B i) sp
  card_stab c := card_stab (hyp B i) sp c.1 _
  Val := ValC (Gr B.emb D.what₂.embLL (D.R.N i)) (B.lam i)
  act := actV B.emb D.what₂.embLL (B.lam i)
  H := ipV B.emb D.what₂.embLL (B.lam i)
  H_act g y y' := ipVal_trFr B.emb D.what₂.embLL (B.lam i) B.fok g y.2 y'.2
  H_pos y hy := (Complex.lt_def.1
    (ClassSumPos.ipVal_pos B.emb D.what₂.embLL (B.lam i) y.1 y.2 fun e => hy (Subtype.ext e))).1
  H_symm y y' := ClassSumPos.ipVal_herm B.emb D.what₂.embLL (B.lam i) y.1 y'.1
  ipV_eq _ _ _ := rfl
  mem_Fi φ := by
    refine forall_congr' fun c => ⟨fun hc => ⟨⟨φ c, hc.1⟩, rfl, fun k hk => ?_⟩, ?_⟩
    · obtain ⟨g, rfl, hg⟩ := (smul_eq_iff (hyp B i) sp k c.1 _ _).1 hk
      exact Subtype.ext (hc.2 ⟨g, hg⟩)
    · rintro ⟨y, e, hy⟩
      refine ⟨e ▸ y.2, fun g => ?_⟩
      rw [e]
      exact congrArg Subtype.val (hy (phi (hyp B i) c.1 g.1) ((smul_eq_iff (hyp B i) sp _ c.1 _ _).2 ⟨g.1, rfl, g.2⟩))
  piL v c x := redL ((B.J.A i).N c.1 ((B.I.S i).rep c)) (B.pr v).1 x
  piL_add _ _ _ hx _ hy := redL_add hx hy
  piL_smul _ _ a _ hx := redL_smul a hx
  piL_surj v c y := by
    obtain ⟨x, hx, e⟩ := redL_surj (M := (B.J.A i).N c.1 ((B.I.S i).rep c)) (P := (B.pr v).1) y
    exact ⟨x, le_locP (B.pr v).1 _ hx, e⟩
  piL_f v c _ hx := fv_redL (hyp B i) (B.lf.lev i) (B.pr v) c hx
  piK v c x := redL ((B.J.A i).dnN c.1 ((B.I.S i).rep c) (B.pr v)) (B.pr v).1 x
  piK_add v c x hx y hy :=
    redL_add ((mem_ker (hyp B i) sp c.1 _ (B.pr v) x).1 hx) ((mem_ker (hyp B i) sp c.1 _ (B.pr v) y).1 hy)
  piK_smul v c a x hx := redL_smul a ((mem_ker (hyp B i) sp c.1 _ (B.pr v) x).1 hx)
  piK_surj v c y := by
    obtain ⟨x, hx, e⟩ := redL_surj (M := (B.J.A i).dnN c.1 ((B.I.S i).rep c) (B.pr v)) (P := (B.pr v).1) y
    exact ⟨x, (mem_ker (hyp B i) sp c.1 _ (B.pr v) x).2 (le_locP (B.pr v).1 _ hx), e⟩
  piK_te v c e he := redL_te (hyp B i) sp (B.lf.lev i) (B.pr v) c e he
  up_eq v c x p₁ hf hp := by
    obtain ⟨a1, a2, a3⟩ := up_spec (hyp B i) sp (B.lf.lev i) (B.pr v) c x p₁ hf hp
    exact ⟨phi (hyp B i) c.1 ((B.I.S i).mv c.1 ((B.J.A i).upPt (B.pr v) c (redL _ (B.pr v).1 x))),
      mk_move (hyp B i) sp c.1 _ _ (B.pr v) p₁ a1 a2 a3, fun _ => rfl⟩
  dn_eq v c γ p₀ hp hf := by
    obtain ⟨a1, a2, a3⟩ := dn_spec (hyp B i) sp (B.pr v) c γ p₀ hp hf
    exact ⟨phi (hyp B i) c.1 ((B.I.S i).mv c.1 ((B.J.A i).dnPt (B.pr v) c γ)),
      mk_move (hyp B i) sp c.1 _ _ (B.pr v) p₀ a1 a2 a3, fun _ => rfl⟩
  dil_eq v c a p' hp := by
    obtain ⟨a1, a2, a3⟩ := dil_spec (hyp B i) sp (B.pr v) c a p' hp
    exact ⟨phi (hyp B i) c.1 ((B.I.S i).mv c.1 ((B.J.A i).diaPt (B.pr v) a c)),
      mk_move (hyp B i) sp c.1 _ _ (B.pr v) p' a1 a2 a3, fun _ => rfl⟩

def real : B.Real i sp (model B i sp) where
  iK _ := RingEquiv.refl B.E
  iK_O _ _ := Iff.rfl
  iK_res P r _ := resP_toO (B.pr P).1 r
  pt b d := mk (hyp B i) sp b 1 d
  hom := phi (hyp B i)
  zeta := MonoidHom.inr (UG B.E (D.R.N i)) _
  pt_smul b g d := (phi_smul (hyp B i) sp b g d).symm
  gen b := by
    intro (k : GG B.E D.what₂.LL (D.R.N i))
    refine ⟨k.2 * (chrT (hyp B i) b (lift sp b k.1))⁻¹, lift sp b k.1, Prod.ext (Subtype.ext ?_) ?_⟩
    · show k.1.1 = 1 * (B.I.S i).gam b _
      rw [one_mul, gam_lift]
    · show k.2 = k.2 * _ * chrT (hyp B i) b _
      rw [inv_mul_cancel_right]
  comm ζ := by
    intro (k : GG B.E D.what₂.LL (D.R.N i))
    exact Prod.ext ((one_mul k.1).trans (mul_one k.1).symm) (mul_comm ζ k.2)
  surj p := by
    obtain ⟨⟨b, ζ, d⟩, e⟩ := mk_surj (hyp B i) sp p
    exact ⟨ζ, b, d, e.symm.trans (inr_smul (hyp B i) sp ζ b d).symm⟩
  idx ζ b b' d d' e :=
    congrArg Sigma.fst ((congrArg Prod.fst (inr_smul (hyp B i) sp ζ b d)).symm.trans e)
  inj ζ b d d' := by
    refine Iff.trans (Eq.congr_left (inr_smul (hyp B i) sp ζ b d)) ((mk_eq_iff (hyp B i) sp b ζ 1 d d').trans ?_)
    refine exists_congr fun g => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
    rw [one_mul, eq_comm]
    exact Subtype.ext_iff
  fst ζ b d d' := by
    refine Iff.trans (Eq.congr_left (congrArg Prod.fst (inr_smul (hyp B i) sp ζ b d)))
      ((mk_fst_iff (hyp B i) sp b ζ 1 d d').trans ?_)
    refine exists_congr fun g => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
    rw [one_mul, eq_comm]
    exact Subtype.ext_iff
  rep_eq _ := rfl
  pt_L _ _ _ _ := Iff.rfl
  pt_f _ _ _ _ := rfl
  loc_hom _ _ _ := Units.ext rfl
  loc_zeta _ _ := rfl
  val_eq := rfl
  act_hom _ _ _ := rfl
  act_zeta ζ y := by
    refine Subtype.ext (funext fun x => ?_)
    refine (trFr_apply B.emb D.what₂.embLL 1 ζ.1 y.1 x).trans ?_
    exact congrArg (fun z => D.what₂.embLL _ * y.1 z)
      ((congrArg (fun g => frMul B.emb D.what₂.embLL g x) inv_one).trans (frMul_one B.emb D.what₂.embLL x))

end Model

theorem exists_real : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T),
    ∃ M : PtModel B.ch i, Nonempty (B.Real i sp M) :=
  fun _ _ B i sp => ⟨model B i sp, ⟨real B i sp⟩⟩

end GlobalTheory.LvT.Built.RealM
