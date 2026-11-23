import Formalism.LocalToGlobal.CharacterGerms.GramMatrixMulRight
import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem mem_vars_subG {Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ℓ ∈ (subG r tau gm plc Q).vars) : ∃ z, ℓ = lam r tau plc z := by
  unfold subG at h
  rw [MvPolynomial.aeval_eq_bind₁] at h
  obtain ⟨y, _, hy⟩ := MvPolynomial.mem_vars_bind₁ _ _ h
  have h1 := MvPolynomial.vars_sum_subset _ _ hy
  rw [Finset.mem_biUnion] at h1
  obtain ⟨col, _, h2⟩ := h1
  have h3 := MvPolynomial.vars_mul _ _ h2
  rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X, Finset.mem_singleton] at h3
  exact ⟨((eW r tau N y).1, col), h3⟩

theorem coS_off (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α : AA r tau N) (col : Fin 2)
    (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) (h : y.1 ≠ α.1) :
    coS r tau gm plc (lam r tau plc (α, col)) y = 0 := by
  have e : y = (eW r tau N).symm ((eW r tau N y).1, (eW r tau N y).2) := by
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [e, coS_lam plc inj, if_neg]
  intro h2
  apply h
  rw [h2]
  rfl

theorem isImgS_subG {dd : ℕ} (X : ∀ o, RawChart C 2 (fun _ => IIs r tau o) (Fin 2 × Fin dd))
    (uv : Letter T r n → Fin dd → C) (e : ∀ o, IIs r tau o → Fin dd → C)
    (hu : ∀ o g (c : IIs r tau o) x, (X o).u g c x = gm o c.1 x.1 g * e o c x.2)
    (huv : ∀ o (c : IIs r tau o) b, uv ⟨tau o c.1, c.2, b⟩ = e o c)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    IsImgS X plc (fun ℓ : Letter T r n => ℓ.2.2) uv (subG r tau gm plc Q) Q := by
  refine ⟨coS r tau gm plc, ?_, (back_subG plc inj gm_hyp Q).symm⟩
  intro ℓ hℓ
  obtain ⟨⟨α, col⟩, rfl⟩ := mem_vars_subG plc hℓ
  refine ⟨α.1, col, rfl, fun ρ' w h => coS_off plc inj α col (ρ', w) h, ?_⟩
  have h1 : (∑ w : (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) (α.1, w) •
      (X w.1).u w.2.1 w.2.2) =
      ∑ y : Fin N × (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) y •
        (X y.2.1).u y.2.2.1 y.2.2.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single α.1]
    · intro ρ' _ hne
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [coS_off plc inj α col (ρ', w) hne, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, sum_coS plc inj α col (fun c y => c • (X y.2.1).u y.2.2.1 y.2.2.2) (fun y => zero_smul _ _)]
  funext x
  rw [Finset.sum_apply]
  have h2 : ∀ g, (Mm r tau gm α col g • (X ((eW r tau N).symm (α, g)).2.1).u ((eW r tau N).symm (α, g)).2.2.1
      ((eW r tau N).symm (α, g)).2.2.2) x = (Gm r tau gm α x.1 g * Mm r tau gm α col g) * e α.2.1 α.2.2 x.2 := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul]
    show Mm r tau gm α col g * (X α.2.1).u g α.2.2 x = _
    rw [hu]
    unfold Gm
    ring
  simp only [h2]
  rw [← Finset.sum_mul, gram_matrix_mul_left gm_hyp α col x.1]
  have h3 : uv (lam r tau plc (α, col)) = e α.2.1 α.2.2 := huv α.2.1 α.2.2 _
  rw [h3]
  split_ifs <;> simp

end Gen

theorem BlockMembershipSelfConjugate.mono {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod 2 → ℕ → ℕ}
    (h : BlockMembershipSelfConjugate X n F FF gaC) (hs : FF ⊆ FF') : BlockMembershipSelfConjugate X n F FF' gaC :=
  fun L h1 h2 pl hpl => hs (h L h1 h2 pl hpl)

section Chart

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem hd_eq_one {ι : T.Fr →+* C} {lab : LabS E C Orb 2} (ha : LabSArith V io ι lab) : lab.hd = 1 := by
  have h := ha.hd_ne
  generalize lab.hd = x at h
  revert x
  decide

theorem gm_mem {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) (t : ZMod 2) (q s : Fin 2) :
    lab.gm o t q s ∈ V.RR := by
  obtain ⟨M, hM⟩ := ha.gm_lim o 0
  have h1 : V.Ge 0 (lab.gm o t q s - emA3 io ι (lab.tau o t) (M q s)) := by simpa using hM t q s
  have h2 := h1.add (hg.em_int o t (M q s))
  rwa [sub_add_cancel] at h2

theorem first_family_subset_image {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by
  intro Po hPo
  refine ⟨subG Dw.mult lab.tau lab.gm plc (∏ o, toAll o (Po o)), hPo, ?_⟩
  exact isImgS_subG plc (fun o => Y.rawSelf (selfOfLab ha hg o))
    (fun (ℓ : LtN Dw n) i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)) (fun o => selfLieBasisVector C3 ι lab o) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) ha.inj (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) _

theorem block_membership_self_conj_charts (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieC Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    BlockMembershipSelfConjugate (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC :=
  (block_membership_self_conj_first Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc h1 h2 h3 first_chern_integral
    (fun o => rdS Y (selfOfLab ha hg) Hy o) F gaC ha.inj (fun o t => by rw [ha.conj o t, hd_eq_one ha])
    (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) (gm_mem ha hg)
    (fun o g x => by
      show (if g = 0 then x.1 else x.1 + lab.hd) = _
      rw [hd_eq_one ha])
    std alt (fun _ => hj) supp tie).mono (first_family_subset_image ha hg a plc)

end Chart

end Formalism.L2.FormalSeriesBounds.RF
