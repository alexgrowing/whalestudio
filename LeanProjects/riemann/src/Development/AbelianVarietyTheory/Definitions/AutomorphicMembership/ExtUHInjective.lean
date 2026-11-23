import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Matrix

section StepOk

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q)
  (pref : DecoF X.E n ST SG Q → Prop)

instance ptYInst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : MulAction (FrmG Λ Θ) (PtY ST SG Q y) := ptYAct y Λ Θ

theorem stepY_gam (b : β) (g : FrmG (Λ b) (Θ b)) (x : Sp X.E n) :
    ((stepY ST y β Λ Θ pref).gam b g : Matrix (Fin n) (Fin n) X.E) *ᵥ x = g.1.1 x := toGLm_mulVec g.1.1 x

theorem stepY_deco (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    (g • p).1.1.deco = ((g.1, g.2.1.1) : UF X.E n × GLG X.E n SG) • p.1.1.deco := rfl

theorem stepY_fr (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) (P : Q) :
    (g • p).1.1.fr P = g.1.1 * p.1.1.fr P * ((g.2.2.1 P)⁻¹).1 := rfl

theorem stepY_eq_one (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) (h : g • p = p)
    (h1 : g.1 = 1) : g = 1 := by
  have h2 : ((g.1, g.2.1.1) : UF X.E n × GLG X.E n SG) • p.1.1.deco = p.1.1.deco := congrArg (fun q => q.1.1.deco) h
  have h3 := DecoSet.eq_one_of_fst_eq_one _ h2 h1
  refine Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h3)) (Subtype.ext (funext fun P => ?_)))
  have h4 : g.1.1 * p.1.1.fr P * ((g.2.2.1 P)⁻¹).1 = p.1.1.fr P := congrArg (fun q => q.1.1.fr P) h
  rw [h1, OneMemClass.coe_one, one_mul, mul_eq_left] at h4
  exact inv_eq_one.1 (Subtype.ext h4)

def stabAut (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    MulAction.stabilizer ((stepY ST y β Λ Θ pref).G b) p →* autO p.1.1.deco.1.N where
  toFun g := ⟨g.1.1.1, g.1.1.2, (congrArg (fun q : PtY ST SG Q y => q.1.1.deco.1.N) g.2 : Formalism.HermitianLatticesTheory.gmap g.1.1.1 p.1.1.deco.1.N = p.1.1.deco.1.N)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabAut_inj (b : β) (p : (stepY ST y β Λ Θ pref).D b) : Function.Injective (stabAut y β Λ Θ pref b p) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact Subtype.ext (stepY_eq_one y β Λ Θ pref b g.1 p g.2 (Subtype.ext (congrArg (fun a : autO p.1.1.deco.1.N => a.1) hg)))

theorem stepY_dvd (hX : X.Ok) (R : Ranks) (hn : n ∈ gamRanks R) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    Nat.card (MulAction.stabilizer ((stepY ST y β Λ Θ pref).G b) p) ∣ DGam X.E R :=
  (Subgroup.card_dvd_of_injective _ (stabAut_inj y β Λ Θ pref b p)).trans
    (dvd_DGam (posStar_of_ok hX) R hn p.1.1.deco.2.lat p.1.1.deco.2.uni)

theorem levQ_grp_idx (Θ : LevQFam X.E X.K n Q) (h : ∀ P, (Θ P).H.FiniteIndex) : Θ.grp.FiniteIndex := by
  have e : Θ.grp = ⨅ P : Q, (Θ P).H.comap (Pi.evalMonoidHom _ P) := by
    ext c
    simp [LevQFam.grp, Subgroup.mem_pi, Subgroup.mem_iInf]
  rw [e]
  refine Subgroup.finiteIndex_iInf fun P => ⟨?_⟩
  rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval P)]
  exact (h P).index_ne_zero

theorem stepY_fin_orb (hX : X.Ok) (hI : ∀ b P, (Θ b P).H.FiniteIndex)
    (hy : ∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) (b : β) :
    Finite (MulAction.orbitRel.Quotient ((stepY ST y β Λ Θ pref).G b) ((stepY ST y β Λ Θ pref).D b)) := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_ok hX)
  have := levQ_grp_idx (Θ b) (hI b)
  let cl : (stepY ST y β Λ Θ pref).D b →
    MulAction.orbitRel.Quotient ((stepY ST y β Λ Θ pref).G b) ((stepY ST y β Λ Θ pref).D b) := Quotient.mk _
  have hcl : ∀ (g : (stepY ST y β Λ Θ pref).G b) p, cl (g • p) = cl p := fun g p => Quotient.sound ⟨g, rfl⟩
  have key : ∀ d0 : DecoSet X.E n ST SG, (cl '' {p | p.1.1.deco = d0}).Finite := by
    intro d0
    rcases Set.eq_empty_or_nonempty {p : (stepY ST y β Λ Θ pref).D b | p.1.1.deco = d0} with h | ⟨p0, hp0⟩
    · rw [h, Set.image_empty]
      exact Set.finite_empty
    · have hp0' : p0.1.1.deco = d0 := hp0
      subst hp0'
      have : Finite (y.ys p0.1.1.deco.1.N) := hy _ p0.1.1.deco.2.lat
      let φ : (GLQ X.E n Q ⧸ (Θ b).grp) × (y.ys p0.1.1.deco.1.N) → (stepY ST y β Λ Θ pref).D b := fun a =>
        ⟨(⟨(p0.1.1.deco, fun P => p0.1.1.fr P * (a.1.out P).1), fun P x => (p0.1.1.2 P _).trans ((a.1.out P).2 x)⟩, a.2.1), a.2.2⟩
      refine (Set.finite_range (cl ∘ φ)).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1.deco = p0.1.1.deco := hp
      let c : GLQ X.E n Q := fun P => ⟨(p0.1.1.fr P)⁻¹ * p.1.1.fr P, fun x => by
        have h1 := p0.1.1.2 P ((p0.1.1.fr P)⁻¹ (p.1.1.fr P x))
        have h2 := p.1.1.2 P x
        have h3 : p0.1.1.1.2 P ((p0.1.1.fr P)⁻¹ (p.1.1.fr P x)) = p.1.1.fr P x := LinearEquiv.apply_symm_apply _ _
        rw [h3] at h1
        have h4 : p.1.1.1.1 = p0.1.1.1.1 := hp'
        rw [h4] at h2
        exact h1.symm.trans h2⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Θ b).grp c
      refine ⟨(QuotientGroup.mk c, ⟨p.1.2, hp' ▸ p.2⟩), ?_⟩
      refine (hcl ((1, 1, k) : FrmG (Λ b) (Θ b)) _).symm.trans (congrArg cl ?_)
      refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ (funext fun P => ?_))) (Set.image_id _))
      · exact (one_smul (UF X.E n × GLG X.E n SG) p0.1.1.deco).trans hp'.symm
      · show (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * (p0.1.1.fr P * ((Quotient.out (QuotientGroup.mk c : GLQ X.E n Q ⧸ (Θ b).grp)) P).1) *
          ((k.1 P)⁻¹).1 = p.1.1.fr P
        rw [hk]
        show (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * (p0.1.1.fr P * (((p0.1.1.fr P)⁻¹ * p.1.1.fr P) * (k.1 P).1)) *
          ((k.1 P).1)⁻¹ = p.1.1.fr P
        group
  rw [← Set.finite_univ_iff]
  refine (hs.biUnion fun d0 _ => key d0).subset ?_
  intro q _
  induction q using Quotient.inductionOn with
  | h p =>
    obtain ⟨d0, hd0, g, hg⟩ := hrep p.1.1.deco
    refine Set.mem_biUnion hd0 ⟨(((g⁻¹, 1, 1) : FrmG (Λ b) (Θ b)) : (stepY ST y β Λ Θ pref).G b) • p, ?_, hcl _ _⟩
    show ((g⁻¹, 1) : UF X.E n × GLG X.E n SG) • p.1.1.deco = d0
    rw [hg, smul_smul, Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    exact one_smul _ d0

theorem stepY_ok (hX : X.Ok) (hI : ∀ b P, (Θ b P).H.FiniteIndex)
    (hr : ∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1)
    (hy : ∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) : (stepY ST y β Λ Θ pref).Ok where
  fin_orb := stepY_fin_orb y β Λ Θ pref hX hI hy
  fin_stab b p :=
    haveI := autO_finite (posStar_of_ok hX) p.1.1.deco.2.lat
    Finite.of_injective _ (stabAut_inj y β Λ Θ pref b p)
  unit b g := by
    have h : Formalism.UG.cT (starRingEnd X.E) (toGLm X.E n g.1.1 : Matrix (Fin n) (Fin n) X.E) * (1 : Matrix (Fin n) (Fin n) X.E) *
      (toGLm X.E n g.1.1 : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ g.1
    rw [Matrix.mul_one] at h
    exact h
  root b g := by
    have h1 : IsOfFinOrder ((Λ b).chr g.2.1) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    have h2 : IsOfFinOrder ((Θ b).chr g.2.2) := by
      rw [show (Θ b).chr g.2.2 = ∏ P, (Θ b P).lam (piProj (fun P => (Θ b P).H) P g.2.2) from
        piChar_apply (fun P => (Θ b P).H) (fun P => (Θ b P).lam) g.2.2]
      exact Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one
        fun P _ => isOfFinOrder_iff_pow_eq_one.2 (hr b P _)
    exact isOfFinOrder_iff_pow_eq_one.1 (h1.mul h2)
  lsh_smul b g p x := by
    rw [stepY_gam]
    show _ ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔ _
    rw [Deco.Lsh_act _ g.1.2, mem_gmap, LinearEquiv.symm_apply_apply]
  lsh_lat b p := p.1.1.deco.2.Lsh_lattice
  stab_inj b g p h h1 := stepY_eq_one y β Λ Θ pref b g p h
    (Subtype.ext ((toGLm X.E n).injective (h1.trans (map_one _).symm)))

theorem stepY_free (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) (w : SG) (hw : w.1 ∈ Pr.vG i)
    (hbig : 2 * X.f * n < Pr.g i - 1)
    (hu : ∀ b, ∀ k ∈ (Λ b w).H, IsNilpotent ((k : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) - 1)) :
    (stepY ST y β Λ Θ pref).Free := by
  intro b g p h
  have h2 : ((g.1, g.2.1.1) : UF X.E n × GLG X.E n SG) • p.1.1.deco = p.1.1.deco := congrArg (fun q => q.1.1.deco) h
  have h3 := DecoSet.decoration_stabilizer_trivial_unipotent hX hPr _ h2 i w hw hbig (hu b _ (g.2.1.2 w (Set.mem_univ w)))
  exact stepY_eq_one y β Λ Θ pref b g p h (congrArg Prod.fst h3)

theorem ptY_nonempty [NeZero n] (h : (y.ys (stdLat X.E n)).Nonempty) : Nonempty (PtY ST SG Q y) := by
  obtain ⟨Y, hY⟩ := h
  exact ⟨⟨(DecoF.base X.E n ST SG Q, Y), hY⟩⟩

end StepOk

section TOk

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q)
  (pref : DecoF X.E n ST SG Q → Prop) (T : ℕ)

theorem PtY.ext' {y : Ys X n} {p p' : PtY ST SG Q y} (h1 : p.1.1.deco = p'.1.1.deco) (h2 : p.1.1.1.2 = p'.1.1.1.2)
    (h3 : p.1.2 = p'.1.2) : p = p' := Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3)

theorem PtY.mv_spec {y : Ys X n} (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG)
    (h1 : ∀ P : Q, d.1.at P.1 = p.1.1.deco.1.at P.1) (h2 : y.ys d.1.N = y.ys p.1.1.deco.1.N) :
    (p.mv d).1.1.deco = d ∧ (p.mv d).1.1.1.2 = p.1.1.1.2 ∧ (p.mv d).1.2 = p.1.2 := by
  have h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N :=
    ⟨fun P x => by rw [h1 P]; exact p.1.1.2 P x, by rw [h2]; exact p.2⟩
  have e : p.mv d = ⟨(⟨(d, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem PtY.mv_dia {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (a : (Res P.1)ˣ) :
    p.mv (DecoSet.dia1 P a p.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ :=
  dif_pos ⟨p.1.1.2, p.2⟩

theorem tdatY_ok (hP : ∀ P : ST, conjPrime₂ P.1 ≠ P.1) (hT : ∀ P : ST, (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) :
    (tdatY ST T y β Λ Θ pref).Ok T where
  N_lat _ p := p.1.1.deco.2.lat
  dnN_lat _ p P := (p.1.1.deco.2.dnN_spec P (hP P)).1
  ker_lat _ p P := by
    have hd := p.1.1.deco.2
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
    refine lattice_of_smul hd.lat hd.Lsh_lattice (Submodule.span_le.2 fun x hx => hx.1) hr0 fun x hx => ?_
    exact Submodule.subset_span ⟨Submodule.smul_mem _ r (hd.N_le_Lsh hx), ((hd.mem_kerAt P _).1 (hd.smul_mem_kerAt P hr hx)).2⟩
  f_add _ p P x hx z hz := p.1.1.deco.2.f_add P x (le_locP _ _ hx) z (le_locP _ _ hz)
  f_smul _ p P a x hx := p.1.1.deco.2.f_smul P a x (le_locP _ _ hx)
  f_ne _ p P := p.1.1.deco.2.f_ne P
  N_act b g p x := by
    rw [stepY_gam]
    show _ ∈ Formalism.HermitianLatticesTheory.gmap g.1.1 p.1.1.deco.1.N ↔ _
    rw [mem_gmap, LinearEquiv.symm_apply_apply]
    rfl
  f_act b g p P x := by
    rw [stepY_gam]
    show p.1.1.deco.1.f P (g.1.1.symm _) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  te_mem _ p P e he h1 := by
    have hd := p.1.1.deco.2
    have he' : e ∈ p.1.1.deco.1.N := he
    have h1' : p.1.1.deco.1.f P e = 1 := h1
    refine ⟨(le_sup_left : p.1.1.deco.1.kerAt P ≤ p.1.1.deco.1.dnN P) (hd.smul_mem_kerAt P (hT P).1 he'), fun hm => ?_⟩
    obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 (hT P).1 (hT P).2
    obtain ⟨c, hc, hcP⟩ := exists_mem_notMem (hP P)
    have h2 : a • ((T : 𝓞 X.E) • e) ∈ p.1.1.deco.1.dnN P := inv_smul_mem ha hm
    have h3 := ((hd.mem_kerAt P _).1 (hd.conj_smul_dnN_mem P hc h2)).2
    have e1 : c • a • ((T : 𝓞 X.E) • e) = (c * r) • e := by
      rw [← algebraMap_smul X.E (T : 𝓞 X.E) e, smul_smul a, mul_comm a, har, algebraMap_smul, mul_smul]
    rw [e1, hd.f_smul P _ e (le_locP _ _ he'), h1', mul_one, Ideal.Quotient.eq_zero_iff_mem] at h3
    exact (P.1.isPrime.mem_or_mem h3).elim hcP hr
  dia_one b P p := by
    classical
    refine (PtY.mv_dia p P 1).trans (PtY.ext' ?_ rfl rfl)
    show DecoSet.dia (Pi.mulSingle P 1) p.1.1.deco = p.1.1.deco
    rw [Pi.mulSingle_one, DecoSet.dia_one]
  dia_mul b P a a' p := by
    classical
    show p.mv (DecoSet.dia1 P (a * a') p.1.1.deco) =
      (p.mv (DecoSet.dia1 P a' p.1.1.deco)).mv (DecoSet.dia1 P a (p.mv (DecoSet.dia1 P a' p.1.1.deco)).1.1.deco)
    rw [PtY.mv_dia, PtY.mv_dia, PtY.mv_dia]
    refine PtY.ext' ?_ rfl rfl
    show DecoSet.dia1 P (a * a') p.1.1.deco = DecoSet.dia1 P a (DecoSet.dia1 P a' p.1.1.deco)
    unfold DecoSet.dia1
    rw [Pi.mulSingle_mul, DecoSet.dia_mul]
  dia_act b P a g p := by
    refine (PtY.mv_dia (g • p) P a).trans ?_
    show _ = g • (p.mv (DecoSet.dia1 P a p.1.1.deco) : (stepY ST y β Λ Θ pref).D b)
    rw [PtY.mv_dia]
    rfl
  dia_N b P a p := by
    show (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.N = _
    rw [PtY.mv_dia]
    rfl
  dia_Lsh b P a p := by
    classical
    show (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.Lsh = p.1.1.deco.1.Lsh
    rw [PtY.mv_dia]
    show (p.1.1.deco.1.dia _).Lsh = _
    unfold Deco.Lsh Deco.L
    congr 2
    ext x
    simp [Deco.dia]
  dia_f b P a p x := by
    classical
    show (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P x = _
    rw [PtY.mv_dia]
    show ((Pi.mulSingle P a : DiaG X.E ST) P).1 * _ = _
    rw [Pi.mulSingle_eq_same]
    rfl

theorem tdatY_deco (b : β) (p : PtY ST SG Q y) :
    (tdatY ST T y β Λ Θ pref).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
  Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))

theorem dn_ok_of_res {d : Deco X.E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {g : Sp X.E n → Res P.1}
    (h : ((d.res (Finset.empty_subset _)).dn P g).Ok) : (d.dn P g).Ok := by
  classical
  have e : ((d.res (Finset.empty_subset _)).dn P g).f P = g := by simp only [Deco.dn, Function.update_self]
  exact hd.dn P hP (e ▸ h.f_add P) (e ▸ h.f_smul P) (e ▸ h.f_off P) (e ▸ h.f_ne P)

variable {y} in
theorem mv_up (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P)
    (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1)
    (hy : y.Off P.1) {x : Sp X.E n} (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)).1.1.deco.1 = p.1.1.deco.1.up P (T : 𝓞 X.E) x ∧
      (p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)).1.1.1.2 = p.1.1.1.2 ∧ (p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)).1.2 = p.1.2 := by
  have e := p.1.1.deco.up_val P hP hT.1 hT.2 hx hf
  have hs := (upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 hP.ne hx).2.2.1
  have h := p.mv_spec (p.1.1.deco.up P (T : 𝓞 X.E) x)
    (fun w => by rw [e]; exact (hs w.1 (hQ w).1 (hQ w).2).localization_eq)
    (hy _ _ fun w h1 h2 => by rw [e]; exact (hs w h1 h2).localization_eq)
  exact ⟨by rw [h.1, e], h.2⟩

variable {y} in
theorem mv_dn (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1)
    (hy : y.Off P.1) {g : Sp X.E n → Res P.1} (hg : (p.1.1.deco.1.dn P g).Ok) :
    (p.mv (p.1.1.deco.dn P g)).1.1.deco.1 = p.1.1.deco.1.dn P g ∧
      (p.mv (p.1.1.deco.dn P g)).1.1.1.2 = p.1.1.1.2 ∧ (p.mv (p.1.1.deco.dn P g)).1.2 = p.1.2 := by
  have e : (p.1.1.deco.dn P g).1 = p.1.1.deco.1.dn P g := by
    unfold DecoSet.dn
    rw [dif_pos hg]
  have hs := (p.1.1.deco.2.dnN_spec P hP.ne).2.2.1
  have h := p.mv_spec (p.1.1.deco.dn P g)
    (fun w => by rw [e]; exact (hs w.1 (hQ w).1 (hQ w).2).localization_eq)
    (hy _ _ fun w h1 h2 => by rw [e]; exact (hs w h1 h2).localization_eq)
  exact ⟨by rw [h.1, e], h.2⟩

theorem tdatY_tied (hP : ∀ P : ST, MoveHyp ST SG P)
    (hT : ∀ P : ST, (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hQ : ∀ (P : ST) (w : Q), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : ∀ P : ST, y.Off P.1) :
    (tdatY ST T y β Λ Θ pref).Tied T where
  ok b p := by rw [tdatY_deco]; exact p.1.1.deco.2.res _
  Lsh_eq _ _ := rfl
  dnN_eq _ _ _ := rfl
  ker_eq _ _ _ := rfl
  up_deco b p P x hx hf := by
    rw [tdatY_deco, tdatY_deco]
    exact congrArg (Deco.res (Finset.empty_subset _)) (mv_up T p P (hP P) (hT P) (hQ P) (hy P) hx hf).1
  dn_deco b p P g hg := by
    rw [tdatY_deco] at hg
    rw [tdatY_deco, tdatY_deco]
    exact congrArg (Deco.res (Finset.empty_subset _))
      (mv_dn p P (hP P) (hQ P) (hy P) (dn_ok_of_res p.1.1.deco.2 P (hP P) hg)).1
  up_act b γ p P x hx hf := by
    rw [stepY_gam]
    have h1 := mv_up T p P (hP P) (hT P) (hQ P) (hy P) hx hf
    have h2 := mv_up T (γ • p) P (hP P) (hT P) (hQ P) (hy P) (x := γ.1.1 x)
      ((mem_gmap γ.1.1 p.1.1.deco.1.N _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx))
      (by show p.1.1.deco.1.f P (γ.1.1.symm _) = 1; rw [LinearEquiv.symm_apply_apply]; exact hf)
    refine PtY.ext' (Subtype.ext (h2.1.trans ?_)) (h2.2.1.trans ?_) (h2.2.2.trans ?_)
    · exact (Deco.up_act _ γ.1.2 _ P _ x).trans (congrArg (Deco.act γ.1.1 γ.2.1.1) h1.1.symm)
    · exact congrArg (fun fr : ∀ _ : Q, Sp X.E n ≃ₗ[X.E] Sp X.E n => fun w => γ.1.1 * fr w * ((γ.2.2.1 w)⁻¹).1) h1.2.1.symm
    · exact congrArg (fun Y : Set (Sp X.E n) => (fun v => γ.1.1 v) '' Y) h1.2.2.symm
  dn_act b γ p P g hg := by
    rw [tdatY_deco] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hP P) hg
    have e : (fun z => g (((stepY ST y β Λ Θ pref).gam b γ⁻¹ : Matrix (Fin n) (Fin n) X.E) *ᵥ z)) = fun z => g (γ.1.1.symm z) :=
      funext fun z => congrArg g (stepY_gam y β Λ Θ pref b γ⁻¹ z)
    rw [e]
    have e2 := Deco.dn_act p.1.1.deco.1 γ.1.2 γ.2.1.1 P g
    have h1 := mv_dn p P (hP P) (hQ P) (hy P) hg'
    have h2 := mv_dn (γ • p) P (hP P) (hQ P) (hy P) (g := fun z => g (γ.1.1.symm z)) (e2 ▸ hg'.act γ.1.2 γ.2.1.1)
    refine PtY.ext' (Subtype.ext (h2.1.trans ?_)) (h2.2.1.trans ?_) (h2.2.2.trans ?_)
    · exact e2.trans (congrArg (Deco.act γ.1.1 γ.2.1.1) h1.1.symm)
    · exact congrArg (fun fr : ∀ _ : Q, Sp X.E n ≃ₗ[X.E] Sp X.E n => fun w => γ.1.1 * fr w * ((γ.2.2.1 w)⁻¹).1) h1.2.1.symm
    · exact congrArg (fun Y : Set (Sp X.E n) => (fun v => γ.1.1 v) '' Y) h1.2.2.symm
  up_congr b p P x x' h := by
    show p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x) = p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x')
    have e := p.1.1.deco.1.up_congr P (T : 𝓞 X.E) h
    congr 1
    unfold DecoSet.up
    generalize p.1.1.deco.1.up P (T : 𝓞 X.E) x = d at e
    subst e
    rfl
  dn_up b p P x hx hf := by
    classical
    have h1 := mv_up T p P (hP P) (hT P) (hQ P) (hy P) hx hf
    have e : (p.1.1.deco.1.up P (T : 𝓞 X.E) x).dn P (p.1.1.deco.1.f P) = p.1.1.deco.1 := by
      refine Deco.ext (p.1.1.deco.2.dnN_up P (hP P) (hT P).1 (hT P).2 hx hf) ?_ rfl
      simp only [Deco.dn, Deco.up, Function.update_idem, Function.update_eq_self]
    have h2 := mv_dn (p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)) P (hP P) (hQ P) (hy P) (g := p.1.1.deco.1.f P)
      (by rw [h1.1, e]; exact p.1.1.deco.2)
    exact PtY.ext' (Subtype.ext (h2.1.trans (by rw [h1.1, e]))) (h2.2.1.trans h1.2.1) (h2.2.2.trans h1.2.2)

theorem Ys.triv_off (P : HeightOneSpectrum (𝓞 X.E)) : (Ys.triv X n).Off P := fun _ _ _ => rfl

end TOk

section AtOk

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem stepAt_ok (hX : X.Ok) (hTp : Tp.Ok) (u : Pr.Word) (j : ℕ)
    (hL : j < R.m → ∀ b P, (L.levQ j b P).H.FiniteIndex ∧ ∀ g, ∃ m : ℕ, 0 < m ∧ (L.levQ j b P).lam g ^ m = 1)
    (hy : ∀ N, Submodule.IsLattice X.E N → ((ysAt R sel mu cst j).ys N).Finite) : (stepAt sel mu cst L Tp u j).Ok := by
  refine stepY_ok _ _ _ _ _ hX ?_ ?_ hy
  · rintro ⟨_ | b, hb⟩ P
    · exact hTp.idx j P
    · exact (hL (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P
    · exact hTp.root j P
    · exact (hL (hb.1 rfl) b P).2

theorem ne_of_T_notMem (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) {w : HeightOneSpectrum (𝓞 X.E)}
    (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) : w ≠ P.1 ∧ w ≠ conjPrime₂ P.1 :=
  ⟨fun e => h (by rw [e]; exact T_mem hPr u P), fun e => h (by rw [e, mem_conjP, map_natCast]; exact T_mem hPr u P)⟩

theorem ysAt_off (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    (j : ℕ) (P : Pr.vT u) : (ysAt R sel mu cst j).Off P.1 := by
  classical
  intro N N' h
  have h1 : ∀ w : rowSG Pr sel mu, Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal N := by
    intro w
    have h2 : (Pr.T u : 𝓞 X.E) ∉ w.1.asIdeal := (Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)
    exact h w.1 (ne_of_T_notMem hPr u P h2).1 (ne_of_T_notMem hPr u P h2).2
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem tdatAt_ok (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (j : ℕ) : (tdatAt sel mu cst L Tp u j).Ok (Pr.T u) :=
  tdatY_ok _ _ _ _ _ _ (fun P => (moveHyp_of_ok hPr u P).ne) (T_unif hX hPr u)

theorem tdatAt_tied (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) :
    (tdatAt sel mu cst L Tp u j).Tied (Pr.T u) :=
  tdatY_tied _ _ _ _ _ _ (moveHyp_of_ok hPr u) (T_unif hX hPr u) (fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (ysAt_off sel mu cst hPr u hQ j)

theorem stepY_dvd_chain {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (hX : X.Ok) (i : ℕ) (hi : i ≤ R.m) (y : Ys X (R.N i))
    (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K (R.N i) SG) (Θ : β → LevQFam X.E X.K (R.N i) Q)
    (pref : DecoF X.E (R.N i) ST SG Q → Prop) (h0 : i = 0 → (stepY ST y β Λ Θ pref).Free) (c : (stepY ST y β Λ Θ pref).Cl) :
    Nat.card ((stepY ST y β Λ Θ pref).Stab c) ∣ DGam X.E R := by
  rcases Nat.eq_zero_or_pos i with h | h
  · have : Subsingleton ((stepY ST y β Λ Θ pref).Stab c) :=
      ⟨fun a b => Subtype.ext ((h0 h c.1 a.1 _ a.2).trans (h0 h c.1 b.1 _ b.2).symm)⟩
    rw [Nat.card_unique]
    exact one_dvd _
  · exact stepY_dvd y β Λ Θ pref hX R (N_mem_gamRanks R h hi) c.1 _

theorem chainAt_ok (hX : X.Ok) (u : Pr.Word) (rho rho' cD Th) (hS : ∀ i, (stepAt sel mu cst L Tp u i).Ok)
    (h0 : (stepAt sel mu cst L Tp u 0).Free) (h1 : ∀ i, i < R.m → ∀ b p, ‖rho i b p‖ = 1)
    (h2 : ∀ i, i < R.m → ∀ b p, ‖rho' i b p‖ = 1) : (chainAt sel mu cst L Tp u rho rho' cD Th).Ok where
  step := hS
  rho_norm i hi _ := h1 i hi _ _
  rho'_norm i hi _ := h2 i hi _ _
  DG_pos := DGam_pos (posStar_of_ok hX) R
  dvd_DG i hi c := stepY_dvd_chain hX i hi _ _ _ _ _ (by rintro rfl; exact h0) c

theorem exists_vG (hX : X.Ok) (hPr : Pr.Ok) : ∃ w : Pr.vGs, w.1 ∈ Pr.vG 0 := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (Pr.vG 0).card by rw [hPr.vG_card 0]; exact hX.f_pos)
  exact ⟨⟨w, Finset.mem_union_left _ hw⟩, hw⟩

theorem stepAt_free (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1)
    (hL : ∀ b, L.levG 0 b = colLev Ch 0) (u : Pr.Word) : (stepAt sel mu cst L Tp u 0).Free := by
  obtain ⟨w, hw⟩ := exists_vG hX hPr
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  refine stepY_free _ _ _ _ _ hX hPr 0 w hw (by rw [hN]; exact hbig) ?_
  rintro ⟨_ | b, hb⟩ k hk
  · exact absurd (hb.2 hm) (by simp)
  · have hk' : k ∈ (L.levG 0 b w).H := hk
    rw [hL, colLev_of_lt Ch hm] at hk'
    exact isNilpotent_of_mem_HX_zero hN.le hk'

end AtOk

section Til

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem iniH_extUH (γ : UF E n) (x : Sp E N) : iniH hN ((extUH hN γ).1 x) = γ.1 (iniH hN x) := by
  subst hN
  exact initL_extE γ.1 x

theorem extUH_last (γ : UF E n) (x : Sp E N) : (extUH hN γ).1 x (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  exact extE_last γ.1 x

theorem extUH_injective : Function.Injective (extUH (E := E) hN) := by
  subst hN
  intro a b h
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have h1 : extE a.1 (incl E n x) = extE b.1 (incl E n x) := congrArg (fun g : UF E (n + 1) => g.1 (incl E n x)) h
  have h2 := congrArg (initL E n) h1
  rwa [initL_extE, initL_extE, initL_incl] at h2

theorem Lsh_empty (d : DecoSet E n ∅ SG) : d.1.Lsh = d.1.N := by
  have h : d.1.L = d.1.N := by
    ext x
    rw [d.2.mem_L]
    exact ⟨fun h => h.1, fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty _)⟩⟩
  unfold Deco.Lsh
  rw [h]
  exact d.2.uni

variable (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
include hT hG

theorem tilH_N (x : Sp E N) : x ∈ (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
    iniH hN x ∈ d.1.Lsh ∧ x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E) := by
  subst hN
  show x ∈ (DecoSet.til (ST := ST) pi d).1.N ↔ _
  rw [DecoSet.til_val d hT hG, Lsh_empty, Submodule.mem_one]
  exact mem_tilN _ _

theorem tilH_f (P : ST) (x : Sp E N) (hx : x ∈ (DecoSet.tilH (ST := ST) hN pi d).1.N) :
    (DecoSet.tilH (ST := ST) hN pi d).1.f P x = redP P.1 (star (pi : E) * x (Br.iL hN)) := by
  subst hN
  change x ∈ (DecoSet.til (ST := ST) pi d).1.N at hx
  show (DecoSet.til (ST := ST) pi d).1.f P x = _
  rw [DecoSet.til_val d hT hG] at hx ⊢
  have : (d.1.til (ST := ST) pi).f P x =
      redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x) := if_pos (le_locP _ _ hx)
  rw [this, hermStd_lastVector_apply]
  rfl

theorem tilH_Lsh (hpi : ∀ P : ST, pi ∈ P.1.asIdeal) (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r) (x : Sp E N) :
    x ∈ (DecoSet.tilH (ST := ST) hN pi d).1.Lsh ↔
      iniH hN x ∈ d.1.Lsh ∧ star (pi : E) * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E) := by
  subst hN
  show x ∈ (DecoSet.til (ST := ST) pi d).1.Lsh ↔ _
  rw [DecoSet.til_val d hT hG, Deco.Lsh, d.2.til_L hT hG hpi hdvd, mem_dual_sup, Lsh_empty]
  refine and_congr ?_ ?_
  · have e : ∀ z : Sp E n, hStd E (n + 1) (incl E n z) x = hStd E n z (initL E n x) := fun z => by
      rw [hStd_succ]; simp
    have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
    show _ ↔ initL E n x ∈ d.1.N
    rw [← hu, mem_dual, mem_dual, hu]
    constructor
    · intro H z hz
      rw [← e]
      exact H _ (Submodule.mem_map_of_mem hz)
    · rintro H _ ⟨z, hz, rfl⟩
      exact (e z).symm ▸ H z hz
  · have e : hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x = star (pi : E) * x (Br.iL rfl) := hermStd_lastVector_apply pi x
    rw [mem_dual, ← e]
    constructor
    · intro H
      exact H _ (Submodule.mem_span_singleton_self _)
    · intro H z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [hStd_osmul_left, LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ H

end Til

namespace Law

open Formalism.L2.Forms

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem tr_one (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp [GStep.tr, trFr_apply, frMul_one]

theorem tr_mul (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  funext y
  simp only [GStep.tr, trFr_apply, map_mul, _root_.mul_inv_rev, frMul_mul, Units.val_mul, mul_assoc]

theorem evV_rho (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem embF_mem (h : (S.fam emb lam).Ok) (x : S.FormsK emb lam h) : S.embF emb σ lam h x ∈ S.Fi emb σ lam := by
  intro c
  refine ⟨evV_mem_ValC emb 1 lam σ _, fun g => ?_⟩
  have h1 : S.rho emb lam c.1 g.1 (x.1 c) = x.1 c := x.2 c g
  show S.tr emb σ c.1 g.1 (evV emb 1 lam σ (x.1 c)) = evV emb 1 lam σ (x.1 c)
  rw [← evV_rho, h1]

theorem cl_rep (c : S.Cl) : S.cl c.1 (S.rep c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) (S.rp_spec b q)

theorem cl_smul (b : S.β) (g : S.G b) (d : S.D b) : S.cl b (g • d) = S.cl b d :=
  congrArg (Sigma.mk b) (Quotient.sound ⟨g, rfl⟩)

theorem val_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    S.trTo emb σ b (g • d) (φ (S.cl b (g • d))) = S.tr emb σ b g (S.trTo emb σ b d (φ (S.cl b d))) := by
  have e : (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) (g • d)) = Quotient.mk _ d := Quotient.sound ⟨g, rfl⟩
  have h1 : S.mv b (g • d) • S.rp b (Quotient.mk _ (g • d)) = g • d := S.mv_smul b (g • d)
  have h2 : S.mv b d • S.rp b (Quotient.mk _ d) = d := S.mv_smul b d
  rw [e] at h1
  have h3 : S.mv b (g • d) = g * S.mv b d := by
    have := hf b ((g * S.mv b d)⁻¹ * S.mv b (g • d)) (S.rp b (Quotient.mk _ d)) (by
      rw [mul_smul, h1, inv_smul_eq_iff, mul_smul, h2])
    exact (inv_mul_eq_one.1 this).symm
  unfold GStep.trTo
  rw [h3, tr_mul, cl_smul]

end General

section Dia

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem diaOne (h : J.Ok) : J.LawDiaOne emb σ := by
  intro P
  ext1 φ
  funext c
  show (I.S 0).trTo emb σ c.1 ((J.A 0).dia c.1 P 1 ((I.S 0).rep c))
    (φ ((I.S 0).cl c.1 ((J.A 0).dia c.1 P 1 ((I.S 0).rep c)))) = φ c
  rw [(h.lev 0).dia_one, cl_rep]
  have h1 := (I.S 0).mv_smul c.1 ((I.S 0).rep c)
  obtain ⟨b, q⟩ := c
  have h2 : (I.S 0).mv b ((I.S 0).rp b q) • (I.S 0).rp b (Quotient.mk _ ((I.S 0).rp b q)) = (I.S 0).rp b q := h1
  rw [(I.S 0).rp_spec] at h2
  have h3 := h.free0 b _ _ h2
  show (I.S 0).tr emb σ b ((I.S 0).mv b ((I.S 0).rp b q)) _ = _
  rw [h3, tr_one]

theorem diaMul (h : J.Ok) : J.LawDiaMul emb σ := by
  intro P a a'
  ext1 φ
  funext c
  obtain ⟨b, q⟩ := c
  show (I.S 0).trTo emb σ b ((J.A 0).dia b P (a * a') ((I.S 0).rp b q)) (φ ((I.S 0).cl b ((J.A 0).dia b P (a * a') ((I.S 0).rp b q)))) =
    (I.S 0).tr emb σ b ((I.S 0).mv b ((J.A 0).dia b P a ((I.S 0).rp b q)))
      ((I.S 0).trTo emb σ b ((J.A 0).dia b P a' ((I.S 0).rep ((I.S 0).cl b ((J.A 0).dia b P a ((I.S 0).rp b q)))))
        (φ ((I.S 0).cl b ((J.A 0).dia b P a' ((I.S 0).rep ((I.S 0).cl b ((J.A 0).dia b P a ((I.S 0).rp b q))))))))
  rw [← val_smul (I.S 0) emb σ h.free0, ← (h.lev 0).dia_act, (I.S 0).mv_smul, ← (h.lev 0).dia_mul, mul_comm a a']

end Dia

section Laws

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]

theorem tr_mem {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (b : S.β) (g : S.G b)
    {F : Fr emb σ n → ℂ} (hF : F ∈ ValC (Gr emb σ n) lam) : S.tr emb σ b g F ∈ ValC (Gr emb σ n) lam := by

  rw [← span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ] at hF ⊢
  have hle : Submodule.span ℂ (Set.range (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)) ≤
      (Submodule.span ℂ (Set.range (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ))).comap
        (S.tr emb σ b g).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ← evV_rho S emb σ lam b g v]
    exact Submodule.subset_span ⟨S.rho emb lam b g v, rfl⟩
  exact hle hF

open Classical in
theorem valC_fd {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by

  rw [← span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ]
  have hle : Submodule.span ℂ (Set.range (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)) ≤
      Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, ← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hle

theorem Fi_fd {n : ℕ} (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := h.fin_orb
  haveI := valC_fd emb σ lam
  let j : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective j fun φ ψ e => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun e c))

theorem mem_Fi {n : ℕ} (S : GStep E K n) (hf : S.Free) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (φ : S.Cl → Fr emb σ n → ℂ) (h : ∀ c, φ c ∈ ValC (Gr emb σ n) lam) : φ ∈ S.Fi emb σ lam := fun c =>
  ⟨h c, fun g => by rw [hf c.1 g.1 _ g.2, tr_one]⟩

theorem Fi_ne_bot {n : ℕ} (S : GStep E K n) (hf : S.Free) (c : S.Cl) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    S.Fi emb σ lam ≠ ⊥ := by
  intro h
  have h1 := mem_Fi S hf emb σ lam (fun _ => evV emb 1 lam σ (extV K lam)) fun _ => evV_mem_ValC emb 1 lam σ _
  rw [h, Submodule.mem_bot] at h1
  exact evV_extV_ne_zero emb 1 lam σ (fr0 emb σ n) (congrFun h1 c)

variable {R : Ranks} {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem atLaws (hI : I.Ok) (h : J.Ok) (hc : ι → HCParam R) : J.Laws emb σ hc where
  one := diaOne J emb σ h
  mul := diaMul J emb σ h
  fd := Fi_fd _ (hI.step 0) emb σ _
  stable := by
    rintro P a _ ⟨φ, hφ, rfl⟩
    exact mem_Fi _ h.free0 emb σ _ _ fun c => tr_mem _ emb σ _ _ _ (hφ _).1

end Laws

end Law

namespace Princ

variable (X : Fields) (Pr : Primes X) (R : Ranks) (u : Pr.Word)

theorem N_succ (j : ℕ) : R.N j = (R.N j - 1) + 1 := by
  have := R.N_pos j
  omega

def lev (n : ℕ) : LevFam X.E X.K n Pr.vGs := fun _ => ⟨⊥, 1⟩

theorem lev_eq_one {n : ℕ} (h : (lev X Pr n).grp) : h = 1 :=
  Subtype.ext (funext fun w => h.2 w (Set.mem_univ w))

def top : TopLev X Pr R ∅ where
  levG j := lev X Pr (R.N j)
  levQ j := LevQFam.top _ _ _ _
  pref u j p := j = R.m → ∃ d, p.deco = DecoSet.tilH (N_succ R j) (Pr.piT u) d

theorem top_ok : (top X Pr R).Ok where
  idx _ P := absurd P.2 (Finset.notMem_empty _)
  root _ P := absurd P.2 (Finset.notMem_empty _)
  levG_top h hh := ⟨1, (map_one _).trans (congrArg Subtype.val (lev_eq_one X Pr ⟨h, hh⟩)).symm⟩
  levQ_last P := absurd P.2 (Finset.notMem_empty _)
  levQ_ini P := absurd P.2 (Finset.notMem_empty _)
  pref_off _ _ h _ e := absurd e h
  pref_top _ _ h := h rfl

variable (Jt : ∀ i, (Formalism.L2.Ker.DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ)

def chainIn : ChainIn X.E X.K X.Tau R where
  S i := stepY (Pr.vT u) (Ys.triv X _) Unit (fun _ => (top X Pr R).levG i) (fun _ => (top X Pr R).levQ i) ((top X Pr R).pref u i)
  rho _ _ := 1
  rho' _ _ := 1
  jet i _ _ := Formalism.L2.Ker.jetMap (Jt i) 0
  DG := DGam X.E R

@[reducible] def stepX : GStep X.E X.K (R.N R.m - 1) :=
  stepY ∅ (Ys.triv X _) Unit (fun _ => lev X Pr _) (fun _ => LevQFam.top _ _ _ ∅) fun _ => True

def perIn (sg : X.Tau → DomWeight (R.N R.m - 1)) : PerIn (chainIn X Pr R u Jt) where
  S' := stepX X Pr R
  b0 := ()
  til _ p := ⟨(⟨(DecoSet.tilH (N_m_succ R) (Pr.piT u) p.1.1.deco, fun P => absurd P.2 (Finset.notMem_empty _)),
    fun P => absurd P.2 (Finset.notMem_empty _)⟩, ∅), rfl⟩
  ext _ := ((extUH (N_m_succ R)).comp (MonoidHom.fst _ _)).prod 1
  sg := sg
  tz := star ((Pr.piT u : 𝓞 X.E) : X.E)
  H _ := ⊤

def atIn (psi : ∀ P : Pr.vT u, AddChar (Res P.1) ℂ) : AtIn (chainIn X Pr R u Jt) where
  T := Pr.T u
  ST := Pr.vT u
  A i := tdatY (Pr.vT u) (Pr.T u) (Ys.triv X _) Unit (fun _ => (top X Pr R).levG i) (fun _ => (top X Pr R).levQ i)
    ((top X Pr R).pref u i)
  psi := psi
  duStar := 1
  Dstar := 1
  GamP := 2

variable {X Pr R}

theorem free (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) : ((chainIn X Pr R u Jt).S 0).Free := by
  obtain ⟨w, hw⟩ := exists_vG hX hPr
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  refine stepY_free _ _ _ _ _ hX hPr 0 w hw (by rw [hN]; exact hbig) fun _ k hk => ?_
  have h : k = 1 := hk
  simp [h]

theorem chainIn_ok (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) : (chainIn X Pr R u Jt).Ok where
  step i := stepY_ok _ _ _ _ _ hX (fun _ => (top_ok X Pr R).idx i) (fun _ => (top_ok X Pr R).root i)
    fun _ _ => Set.finite_singleton _
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  DG_pos := DGam_pos (posStar_of_ok hX) R
  dvd_DG i hi c := stepY_dvd_chain hX i hi _ _ _ _ _ (by rintro rfl; exact free u Jt hX hPr hbig) c

theorem cl_nonempty (i : ℕ) : Nonempty ((chainIn X Pr R u Jt).S i).Cl := by
  have : NeZero (R.N i) := ⟨(R.N_pos i).ne'⟩
  obtain ⟨p⟩ := ptY_nonempty (ST := Pr.vT u) (SG := Pr.vGs) (Q := ∅) (Ys.triv X (R.N i)) ⟨∅, rfl⟩
  exact ⟨((chainIn X Pr R u Jt).S i).cl () p⟩

theorem stepX_ok (hX : X.Ok) : (stepX X Pr R).Ok :=
  stepY_ok _ _ _ _ _ hX (fun _ P => absurd P.2 (Finset.notMem_empty _)) (fun _ P => absurd P.2 (Finset.notMem_empty _))
    fun _ _ => Set.finite_singleton _

theorem perIn_ok (hX : X.Ok) (hPr : Pr.Ok) (sg : X.Tau → DomWeight (R.N R.m - 1)) : (perIn X Pr R u Jt sg).Ok where
  step := stepX_ok hX
  til_smul _ g p := by
    refine PtY.ext' ?_ (funext fun P => absurd P.2 (Finset.notMem_empty _)) (Set.image_empty _).symm
    refine (DecoSet.tilH_smul (N_m_succ R) (g.1, g.2.1.1) p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)).trans ?_
    rw [lev_eq_one X Pr g.2.1]
    show (extUH (N_m_succ R) g.1, extGH (N_m_succ R) 1) • _ = _
    rw [map_one]
    rfl
  ext_inj _ a b h := Prod.ext (extUH_injective _ (congrArg Prod.fst h))
    (Prod.ext ((lev_eq_one X Pr _).trans (lev_eq_one X Pr _).symm)
      (Subtype.ext (funext fun P => absurd P.2 (Finset.notMem_empty _))))
  gam_ini _ g x := (congrArg (iniH (N_m_succ R)) (toGLm_mulVec (extUH (N_m_succ R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := by
    have h1 : g.2.2 = 1 := Subtype.ext (funext fun P => absurd P.2 (Finset.notMem_empty _))
    show (lev X Pr (R.N R.m)).chr 1 * (LevQFam.top X.E X.K (R.N R.m) ∅).chr 1 =
      (lev X Pr (R.N R.m - 1)).chr g.2.1 * (LevQFam.top X.E X.K (R.N R.m - 1) ∅).chr g.2.2
    have h2 : (lev X Pr (R.N R.m - 1)).chr g.2.1 = 1 := (congrArg _ (lev_eq_one X Pr g.2.1)).trans (map_one _)
    have h3 : (LevQFam.top X.E X.K (R.N R.m - 1) ∅).chr g.2.2 = 1 := (congrArg _ h1).trans (map_one _)
    rw [h2, h3, map_one, map_one]
  tz_ne := by
    show star ((Pr.piT u : 𝓞 X.E) : X.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : Pr.piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til _ p x := tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
    (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem hX hPr u) x
  rep_til b p := by
    have hex : ∃ q : PtY (Pr.vT u) Pr.vGs ∅ (Ys.triv X (R.N R.m)),
        Quotient.mk (MulAction.orbitRel (FrmG ((top X Pr R).levG R.m) ((top X Pr R).levQ R.m)) _) q =
        Quotient.mk _ ((perIn X Pr R u Jt sg).til b p) ∧ (top X Pr R).pref u R.m q.1.1 := ⟨_, rfl, fun _ => ⟨_, rfl⟩⟩
    have e : ((chainIn X Pr R u Jt).S R.m).rep (((chainIn X Pr R u Jt).S R.m).cl () ((perIn X Pr R u Jt sg).til b p)) =
        hex.choose := dif_pos hex
    obtain ⟨d, hd⟩ := hex.choose_spec.2 rfl
    refine ⟨(), ⟨(⟨(d, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩, ∅), rfl⟩,
      e.trans (PtY.ext' hd (funext fun P => absurd P.2 (Finset.notMem_empty _)) hex.choose.2)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩

theorem perIn_over (hPr : Pr.Ok) (sg : X.Tau → DomWeight (R.N R.m - 1)) (psi : ∀ P : Pr.vT u, AddChar (Res P.1) ℂ) :
    (perIn X Pr R u Jt sg).Over (atIn X Pr R u Jt psi) where
  norm_tz := by
    show star (star ((Pr.piT u : 𝓞 X.E) : X.E)) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til _ p x := tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til _ p P x hx := tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx

theorem atIn_ok (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hf : X.f = R.f) :
    ∃ psi, (atIn X Pr R u Jt psi).Ok := by
  have hpsi : ∀ P : Pr.vT u, ∃ ψ : AddChar (Res P.1) ℂ, ψ ≠ 1 := by
    intro P
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : Res P.1))).2 one_ne_zero
    exact ⟨ψ, fun h => hψ (by rw [h]; rfl)⟩
  choose psi hpsi using hpsi
  exact ⟨psi, hPr.T_prime u, (hPr.vT_card u).trans hf, fun P => hPr.vT_norm u P.1 P.2,
    fun i => tdatY_ok _ _ _ _ _ _ (fun P => (moveHyp_of_ok hPr u P).ne) (T_unif hX hPr u),
    fun i => tdatY_tied _ _ _ _ _ _ (moveHyp_of_ok hPr u) (T_unif hX hPr u)
      (fun _ w => absurd w.2 (Finset.notMem_empty _)) fun P => Ys.triv_off P.1,
    hpsi, free u Jt hX hPr hbig, Nat.one_pos, one_pos, one_lt_two⟩

def fmIn {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {R : Ranks} {I : ChainIn E K ι R}
    (J : AtIn I) (Pl : Rows.Places K) (e : J.ST ≃ ι) : FmIn J Pl where
  tauOf _ := e
  seenP _ := true
  beOn _ := 1
  beOn_nonneg _ := zero_le_one
  thFree _ _ _ _ := 1
  thFree_nonneg _ _ _ _ := zero_le_one

theorem all_ok (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hf : X.f = R.f) (u : Pr.Word)
    (sg : X.Tau → DomWeight (R.N R.m - 1)) (hc : X.Tau → HCParam R) (Pl : Rows.Places X.K) :
    ∃ (σ : X.K →+* ℂ) (I : ChainIn X.E X.K X.Tau R) (J : AtIn I) (Q : PerIn I), FOk X.emb σ ∧ I.Ok ∧ J.Ok ∧ Q.Ok ∧ Q.Over J ∧
      J.Laws X.emb σ hc ∧ Nonempty (FmIn J Pl) ∧ (∀ i, Nonempty (I.S i).Cl) ∧ (I.S 0).Fi X.emb σ (lamT hc 0) ≠ ⊥ ∧
      I.DG = DGam X.E R := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  obtain ⟨psi, hJ⟩ := atIn_ok u (fun _ _ => 1) hX hPr hbig hf
  have hI := chainIn_ok u (fun _ _ => 1) hX hPr hbig
  obtain ⟨c⟩ := cl_nonempty (R := R) u (fun _ _ => 1) 0
  refine ⟨σ, _, _, perIn X Pr R u _ sg, ⟨hX.conjE, hX.emb_star, hσ⟩, hI, hJ, perIn_ok u _ hX hPr sg, perIn_over u _ hPr sg psi,
    Law.atLaws _ _ _ hI hJ hc, ⟨fmIn _ Pl (Fintype.equivOfCardEq ?_)⟩, cl_nonempty u _, Law.Fi_ne_bot _ hJ.free0 c _ _ _, rfl⟩
  exact (Fintype.card_coe _).trans (hPr.vT_card u)

end Princ

section Checks

example {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
    (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ) (h : I.Ok) (hc : ι → HCParam R) :
    (I.chain emb σ h hc).DGam = I.DG := rfl

example (R : Ranks) : R.N R.m - 1 ∈ gamRanks R ∧ R.nV ∈ gamRanks R := ⟨pred_mem_gamRanks R, nV_mem_gamRanks R⟩

end Checks

end GlobalTheory.Mem.Col2

end
