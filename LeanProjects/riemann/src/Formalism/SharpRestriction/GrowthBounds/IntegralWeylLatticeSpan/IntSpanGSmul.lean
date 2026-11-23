import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescent

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

section Gen

variable {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

theorem intSpanG_smul (embLL : LL →+* ℂ) (R0 : Subring LL) (lam : Tau → DomWeight n) (a : LL) (ha : a ∈ R0)
    {P : MvPolynomial (Tau × Fin n × Fin n) ℂ} (hP : P ∈ IntSpanG embLL R0 lam) : embLL a • P ∈ IntSpanG embLL R0 lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨a * s, f, mul_mem ha hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem fnOf_congr (G : Tau → Matrix (Fin n) (Fin n) ℂ) (s : Tau → ℤ) (M M' : Tau → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Tau × Fin n × Fin n) ℂ) (y y' : Frames G) (h : ∀ τ, M τ * y.1 τ = M' τ * y'.1 τ) :
    fnOf G s M P y = fnOf G s M' P y' := by
  show (∏ τ, (M τ * y.1 τ).det ^ s τ) * MvPolynomial.eval (fun x : Tau × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P =
    (∏ τ, (M' τ * y'.1 τ).det ^ s τ) * MvPolynomial.eval (fun x : Tau × Fin n × Fin n => (M' x.1 * y'.1 x.1) x.2.1 x.2.2) P
  simp only [h]

end Gen

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module LL V] {embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem atInf_bc (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (τ : Tau) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ = ((bc (emb τ) γ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := rfl

def trF (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bc (emb τ) γ).isUnit).mul (z.2 τ)⟩

theorem isTr_trF (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z (trF emb γ z) := fun _ => rfl

theorem isTr_trF_inv (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) (trF emb γ⁻¹ z) z := by
  intro τ
  show z.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [atInf_bc, atInf_bc, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem valIntAt_of (hcore : WeylLatticeDescent) (hfrac : IsFractionRing G.O G.Kf)
    (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (R0 : Subring LL) (hR0 : ∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap G.O G.Kf))
    (lam : Tau → DomWeight n) (hw : WtTie G.P A.rk pos lam)
    (hex : ValEx S emb embLL G A pos embV yc)
    (Bas : cls → GL (Fin n) E → Prop) (hBex : ∀ c, ∃ B', Bas c B')
    (hlat : ∀ (i : G.comp) (L : G.P.Tup) (c : cls) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U),
      (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      γ ∈ UJ (σ : E →+* E) J → A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
      ∀ B', Bas c B' → ∀ v (s : Fin (G.P.n' v)), extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
        colSpan G.O ((nAt G.P A.rk pos (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) v s).map e))
    (hchi : ∀ κ : S.U, ∃ r ∈ R0, r⁻¹ ∈ R0 ∧ embLL r = (S.chi κ : ℂ)) :
    ValIntAt S emb embLL G e A pos embV yc (fun x c => ∀ B', Bas c B' → ∃ P ∈ IntSpanG embLL R0 lam,
      ∀ z, embV x c z = fnOf _ (shiftOf lam) (atInf emb ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P z) := by
  rintro x i L c hL ⟨g, γ, κ, hg, hγ, hpt⟩
  have hQ := valC_spec hex x i L hL
  have hval := hQ.2 g hg c γ hγ κ hpt
  have hcmp : cmpC S emb embLL G e A pos embV yc x i L = MvPolynomial.map e (valC S emb embLL G A pos embV yc x i L) := by
    unfold cmpC; rw [if_pos hL]
  rw [hcmp]
  obtain ⟨r, hr, hr', hrχ⟩ := hchi κ
  have hr0 : embLL r ≠ 0 := by rw [hrχ]; exact (S.chi κ).ne_zero
  have hM : (fun τ => ((bc (tE τ) A.B⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).map embLL) = crdB emb A.B := by
    funext τ; ext a b; exact htE τ _
  have hNM : ∀ B' : GL (Fin n) E, (fun τ => (((bc (tE τ) (A.B⁻¹ * γ * B'))⁻¹ * bc (tE τ) A.B⁻¹ : GL (Fin n) LL) :
      Matrix (Fin n) (Fin n) LL).map embLL) = atInf emb ((B'⁻¹ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    intro B'
    funext τ
    have e1 : (bc (tE τ) (A.B⁻¹ * γ * B'))⁻¹ * bc (tE τ) A.B⁻¹ = bc (tE τ) (B'⁻¹ * γ⁻¹) := by
      rw [← map_inv, ← map_mul]; congr 1; group
    rw [e1]
    ext a b; exact htE τ _
  have hfn : ∀ (B' : GL (Fin n) E) (Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z z' : Frames (gramC J emb)),
      IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z' z →
      fnOf (gramC J emb) (shiftOf lam) (atInf emb ((B'⁻¹ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) Pp z =
        fnOf (gramC J emb) (shiftOf lam) (atInf emb ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) Pp z' := by
    intro B' Pp z z' hz
    refine fnOf_congr _ _ _ _ _ _ _ fun τ => ?_
    rw [hz τ, atInf_bc, atInf_bc, atInf_bc, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul]
    congr 3
    group
  have hc := fun B' (hB' : Bas c B') => hcore G.P A.rk pos (gramC J emb) embLL e R0 hfrac hR0 lam hw (fun τ => bc (tE τ) A.B⁻¹)
    (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) L (hlat i L c g γ κ hg hγ hpt B' hB') (valC S emb embLL G A pos embV yc x i L)
  constructor
  · intro hmem B' hB'
    obtain ⟨Pp, hPp, hev⟩ := (hc B' hB').1 hmem
    refine ⟨embLL r⁻¹ • Pp, intSpanG_smul _ _ _ _ hr' hPp, fun z' => ?_⟩
    have h1 := hev (trF emb γ z')
    rw [hM, hNM, hval _ z' (isTr_trF emb γ z'), hfn B' Pp _ z' (isTr_trF emb γ z'), ← hrχ] at h1
    rw [map_smul, Pi.smul_apply, ← h1, smul_eq_mul, map_inv₀, inv_mul_cancel_left₀ hr0]
  · intro hI
    obtain ⟨B', hB'⟩ := hBex c
    obtain ⟨Pp, hPp, hev⟩ := hI B' hB'
    refine (hc B' hB').2 ⟨embLL r • Pp, intSpanG_smul _ _ _ _ hr hPp, fun z => ?_⟩
    rw [hM, hNM, hval z _ (isTr_trF_inv emb γ z), hfn B' _ z _ (isTr_trF_inv emb γ z), map_smul, Pi.smul_apply, ← hev, hrχ,
      smul_eq_mul]

end Gen2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def RestExB (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → ∀ c : (D.mem u).C.cls 0,
    ∃ B' : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B'

def RestChi (T : ∀ u : D.what₂.Word, Forms0 D u) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    ∀ κ : ((T u).cls0).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
      D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ)

def RestLatO (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop :=
  ∀ u w hg (i : (D.gat u w hg).comp) (L : (D.gat u w hg).P.Tup) (c : (D.mem u).C.cls 0)
    (g : ∀ v, GL (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (κ : ((T u).cls0).lev.U),
    (∀ v, L v = colSpan ((D.gat u w hg).P.W v) (g v : Matrix (Fin ((D.gat u w hg).P.m + 1)) (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v))) →
    γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    (locAt X u w hg I.B).IsPt i g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((T u).cls0).y c).1 * κ.1) →
    ∀ B' : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B' →
    ∀ v (s : Fin ((D.gat u w hg).P.n' v)),
      extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v) =
        colSpan (D.gat u w hg).O ((nAt (D.gat u w hg).P (locAt X u w hg I.B).rk (Gt.gat_pos u w hg)
          (fun τ => bc (tEL D τ) ((locAt X u w hg I.B).B⁻¹ * γ * B')) v s).map (I.embW u w hg))

set_option maxHeartbeats 4000000 in

theorem valIntRec_of {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (hcore : WeylLatticeDescent)
    (hex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
      (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y)
    (hfrac : ∀ u w hg, IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hB : RestExB D) (hlat : RestLatO T Gt I) (hchi : RestChi T) : ValIntRec T Gt I := by
  intro u w hg x i L c hL hpt
  have h := valIntAt_of (S := ((T u).cls0).lev) (emb := embT D) (embLL := D.what₂.embLL) (G := D.gat u w hg)
    (e := I.embW u w hg) (A := locAt X u w hg I.B) (pos := Gt.gat_pos u w hg) (embV := embFr T u)
    (yc := ((T u).cls0).y) hcore (hfrac u w hg) (tEL D) (tEL_emb D) (intW D.what₂.places w)
    (fun a => I.embW_int u w hg a) ((D.fm u).lam 0) (fun v s i => Gt.gat_lam u w hg v s i) (hex u w hg)
    (fun c B' => Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B')
    (hB u w hg) (hlat u w hg) (hchi u w hg) x i L c hL hpt
  rw [h]
  constructor
  · intro h1 B' hB'
    obtain ⟨P, hP, hz⟩ := h1 B' hB'
    refine ⟨P, hP, fun z => ?_⟩
    have := hz (((T u).val0).eY z)
    rw [lamT_zero]
    rw [← this]
    show _ = (D.fm u).emb 0 x c (((T u).val0).eY.symm (((T u).val0).eY z))
    rw [Equiv.symm_apply_apply]
  · intro h1 B' hB'
    obtain ⟨P, hP, hz⟩ := h1 B' hB'
    refine ⟨P, hP, fun z => ?_⟩
    have := hz (((T u).val0).eY.symm z)
    rw [lamT_zero, Equiv.apply_symm_apply] at this
    exact this

end Formalism.L2.G.RelativeIndexFlags
