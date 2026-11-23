import Mathlib
import Formalism.SatakeDualWeyl.StatementG
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Compl

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

def complMap (h : w.under (𝓞 F) = v) : Fv F v →+* w.adicCompletion E := by
  subst h; exact GlobalTheory.AdeleBaseChange.locMap F w

theorem complMap_rfl (w : HeightOneSpectrum (𝓞 E)) :
    complMap (rfl : w.under (𝓞 F) = _) = GlobalTheory.AdeleBaseChange.locMap F w := rfl

theorem complMap_algebraMap (h : w.under (𝓞 F) = v) (x : F) :
    complMap h (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := by
  subst h; exact GlobalTheory.AdeleBaseChange.locMap_algebraMap w x

theorem complMap_mem (h : w.under (𝓞 F) = v) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    complMap h a ∈ Ov E w := by
  subst h; exact GlobalTheory.AdeleBaseChange.locMap_int w a ha

def toCompl (h : w.under (𝓞 F) = v) : Fv F v ⊗[F] E →+* w.adicCompletion E :=
  letI : Algebra F (w.adicCompletion E) := ((algebraMap E (w.adicCompletion E)).comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap (⟨complMap h, complMap_algebraMap h⟩ : Fv F v →ₐ[F] w.adicCompletion E)
    (⟨algebraMap E _, fun _ => rfl⟩ : E →ₐ[F] w.adicCompletion E)).toRingHom

@[simp] theorem toCompl_tmul (h : w.under (𝓞 F) = v) (a : Fv F v) (x : E) :
    toCompl h (a ⊗ₜ[F] x) = complMap h a * algebraMap E _ x := rfl

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

def locMat (h : w.under (𝓞 F) = v) : GLoc σ J v →* GL (Fin n) (w.adicCompletion E) :=
  (bc (toCompl h)).comp (matHom _ σ J)

variable (w) in

def latAt : Submodule (Ov E w) (Fin n → w.adicCompletion E) :=
  Submodule.span (Ov E w) ((fun x i => algebraMap E (w.adicCompletion E) (x i)) '' (L : Set (Fin n → E)))

variable (w) in

def IsFrameAt (a : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ y : Fin n → w.adicCompletion E, (∀ i, y i ∈ Ov E w) ↔ a.1 *ᵥ y ∈ latAt w L

def IsSplitChart (h : w.under (𝓞 F) = v) (e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)) : Prop :=
  (∃ a, IsFrameAt w L a ∧ ∀ g, e g = a⁻¹ * locMat σ J h g * a) ∧ ∀ g, g ∈ stabLoc σ J L v ↔ e g ∈ KGL w n

def IsConjAt (h : w.under (𝓞 F) = v) (c : w.adicCompletion E →+* w.adicCompletion E) : Prop :=
  ∀ y, c (toCompl h y) = toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y)

def IsInertChart (h : w.under (𝓞 F) = v) (c : w.adicCompletion E →+* w.adicCompletion E)
    (e : GLoc σ J v ≃* GU c n) : Prop :=
  IsConjAt σ h c ∧
    (∃ a, IsFrameAt w L a ∧ cT c a.1 * J.map (algebraMap E _) * a.1 = antiJ _ n ∧
      ∀ g, (e g : GL (Fin n) (w.adicCompletion E)) = a⁻¹ * locMat σ J h g * a) ∧
    ∀ g, g ∈ stabLoc σ J L v ↔ e g ∈ KU c n

variable {σ J L}

theorem IsFrameAt.inv_mul_mem {a b : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a) (hb : IsFrameAt w L b) :
    a⁻¹ * b ∈ KGL w n := by
  have e := Final.StabStd (w.adicCompletion E) (Ov E w) (Fin n) Subtype.val_injective
  have hm : ∀ y : Fin n → w.adicCompletion E, y ∈ stdLat (n := Fin n) (Ov E w) ↔ ∀ i, y i ∈ Ov E w := fun y =>
    ⟨fun h i => by obtain ⟨r, hr⟩ := h i trivial; exact hr ▸ r.2, fun h i _ => ⟨⟨_, h i⟩, rfl⟩⟩
  refine e.le fun y => ?_
  rw [hm, hm, hb, ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]

theorem IsSplitChart.exists_conj {h : w.under (𝓞 F) = v} {e e' : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)}
    (he : IsSplitChart σ J L h e) (he' : IsSplitChart σ J L h e') : ∃ k ∈ KGL w n, ∀ g, e' g = k⁻¹ * e g * k := by
  obtain ⟨⟨a, ha, e1⟩, -⟩ := he
  obtain ⟨⟨b, hb, e2⟩, -⟩ := he'
  exact ⟨_, ha.inv_mul_mem hb, fun g => by rw [e1, e2]; group⟩

theorem IsInertChart.exists_conj {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}
    {e e' : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) (he' : IsInertChart σ J L h c e') :
    ∃ k ∈ KU c n, ∀ g, e' g = k⁻¹ * e g * k := by
  obtain ⟨-, ⟨a, ha, ha', e1⟩, -⟩ := he
  obtain ⟨-, ⟨b, hb, hb', e2⟩, -⟩ := he'
  have hk : a⁻¹ * b ∈ GU c n := by
    change cT c (a⁻¹ * b).1 * antiJ _ n * (a⁻¹ * b).1 = antiJ _ n
    conv_lhs => rw [← ha']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_left, hb']
  exact ⟨⟨_, hk⟩, ⟨hk, ha.inv_mul_mem hb⟩, fun g => Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, e1, e2]; group)⟩

end Compl

section Param

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsParamVec (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (B : Multiset ℂˣ) : Prop :=
  (IsSplit (E := E) v ∧ ∃ e, IsSplitChart σ J L h e ∧ IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x B) ∨
  (IsInertAt F E v w ∧ ∃ c ϖ e α, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧
    IsSatVecU ϖ (qV F v) (ρ.comp e.symm.toMonoidHom) x α ∧ B = bcParam n α)

def HasParam (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (B : Multiset ℂˣ) : Prop :=
  (IsSplit (E := E) v ∧ ∃ e, IsSplitChart σ J L h e ∧ HasSatGL w (ρ.comp e.symm.toMonoidHom) B) ∨
  (IsInertAt F E v w ∧ ∃ c ϖ e α, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧
    HasSatU ϖ (qV F v) (ρ.comp e.symm.toMonoidHom) α ∧ B = bcParam n α)

open Classical in

def paramOf (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) : Multiset ℂˣ :=
  if hB : ∃ B, HasParam σ J L h ρ B then hB.choose else 0

variable (n) in

def IsSysParam (h : w.under (𝓞 F) = v) (c : List ℤ → ℂ) (B : Multiset ℂˣ) : Prop :=
  (IsSplit (E := E) v ∧ B.card = n ∧
    ∀ j ≤ n, c (List.replicate j 1 ++ List.replicate (n - j) 0) = satEig (qV E w) n B j) ∨
  (IsInertAt F E v w ∧ ∃ τ ϖ α, IsUnramInv ϖ τ (qV F v) ∧ IsConjAt σ h τ ∧ B = bcParam n α ∧
    ∀ (d : Fin n → ℤ) (t : GU τ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      c (List.ofFn d) = SatU ϖ (qV F v) (dosetInd ℂ (KU τ n) t) fun i => (α i : ℂ))

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem not_isSplit_of_isInertAt (hw : IsInertAt F E v w) : ¬ IsSplit (E := E) v := by
  rintro ⟨P, Q, hne, hP, hQ⟩
  have key : ∀ R : HeightOneSpectrum (𝓞 E), R.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal → w = R :=
    fun R hR => HeightOneSpectrum.ext (w.isMaximal.eq_of_le R.isPrime.ne_top
      (hw ▸ Ideal.map_le_iff_le_comap.2 hR.ge))
  exact hne ((key P hP).symm.trans (key Q hQ))

theorem IsParamVec.ne_zero (hx : IsParamVec σ J L h ρ x B) : x ≠ 0 := by
  rcases hx with ⟨-, e, -, hx⟩ | ⟨-, c, ϖ, e, α, -, -, hx, -⟩ <;> exact hx.1

theorem IsParamVec.mem_fixed (hx : IsParamVec σ J L h ρ x B) : x ∈ fixed ρ (stabLoc σ J L v) := by
  rcases hx with ⟨-, e, he, hx⟩ | ⟨-, c, ϖ, e, α, -, he, hx, -⟩
  · exact (mem_fixed_comp_symm e he.2).1 hx.2.1
  · exact (mem_fixed_comp_symm e he.2.2).1 hx.2.1

theorem IsParamVec.card (hx : IsParamVec σ J L h ρ x B) : B.card = n := by
  rcases hx with ⟨-, e, -, hx⟩ | ⟨-, c, ϖ, e, α, -, -, -, rfl⟩
  · exact hx.2.2.1
  · exact GlobalTheory.LGrp.card_bcParam n α

theorem HasParam.isParamVec (hρ : HasParam σ J L h ρ B) (hx : x ∈ fixed ρ (stabLoc σ J L v)) (h0 : x ≠ 0) :
    IsParamVec σ J L h ρ x B := by
  rcases hρ with ⟨hv, e, he, hρ⟩ | ⟨hv, c, ϖ, e, α, hU, he, hρ, hB⟩
  · exact Or.inl ⟨hv, e, he, hρ.2 x ((mem_fixed_comp_symm e he.2).2 hx) h0⟩
  · exact Or.inr ⟨hv, c, ϖ, e, α, hU, he, hρ.2 x ((mem_fixed_comp_symm e he.2.2).2 hx) h0, hB⟩

theorem HasParam.exists_vec (hρ : HasParam σ J L h ρ B) : ∃ x, IsParamVec σ J L h ρ x B := by
  rcases hρ with ⟨hv, e, he, hρ⟩ | ⟨hv, c, ϖ, e, α, hU, he, hρ, hB⟩
  · exact hρ.exists_vec.imp fun x hx => Or.inl ⟨hv, e, he, hx⟩
  · exact hρ.exists_vec.imp fun x hx => Or.inr ⟨hv, c, ϖ, e, α, hU, he, hx, hB⟩

theorem HasParam.isSpherical (hρ : HasParam σ J L h ρ B) : GlobalTheory.LGrp.IsSpherical ρ (stabLoc σ J L v) := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact (Submodule.ne_bot_iff _).2 ⟨x, hx.mem_fixed, hx.ne_zero⟩

theorem IsParamVec.isSatVecGL (hx : IsParamVec σ J L h ρ x B) (hv : IsSplit (E := E) v)
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) :
    IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x B := by
  have hf := hx.mem_fixed
  rcases hx with ⟨-, e', he', hx⟩ | ⟨hw, -⟩
  · obtain ⟨k, hk, hc⟩ := he'.exists_conj he
    exact ⟨hx.1, (mem_fixed_comp_symm e he.2).2 hf, hx.2.2.1, fun ϖ hϖ j hj => by
      rw [heckeVec_comp_symm_congr e' e he'.2 hk hc (Tj_mem_hecke hϖ j).1 hf, hx.2.2.2 ϖ hϖ j hj]⟩
  · exact absurd hv (not_isSplit_of_isInertAt hw)

theorem IsSatVecU.of_chart {c : w.adicCompletion E →+* w.adicCompletion E} {e e' : GLoc σ J v ≃* GU c n}
    (he : IsInertChart σ J L h c e) (he' : IsInertChart σ J L h c e') {ϖ : w.adicCompletion E} {q : ℕ}
    {α : Fin (n / 2) → ℂˣ} (hx : IsSatVecU ϖ q (ρ.comp e.symm.toMonoidHom) x α) :
    IsSatVecU ϖ q (ρ.comp e'.symm.toMonoidHom) x α := by
  have hf := (mem_fixed_comp_symm e he.2.2).1 hx.2.1
  obtain ⟨k, hk, hc⟩ := he.exists_conj he'
  exact ⟨hx.1, (mem_fixed_comp_symm e' he'.2.2).2 hf, fun t ht => by
    rw [heckeVec_comp_symm_congr e e' he.2.2 hk hc ht.1 hf, hx.2.2 t ht]⟩

theorem IsParamVec.unique_of_isSplit (hv : IsSplit (E := E) v) (hx : IsParamVec σ J L h ρ x B)
    (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  rcases hx' with ⟨-, e, he, hx'⟩ | ⟨hw, -⟩
  · exact (hx.isSatVecGL hv he).unique hx'
  · exact absurd hv (not_isSplit_of_isInertAt hw)

theorem HasParam.hasParam_paramOf (hρ : HasParam σ J L h ρ B) : HasParam σ J L h ρ (paramOf σ J L h ρ) := by
  rw [paramOf, dif_pos ⟨B, hρ⟩]
  exact Exists.choose_spec (⟨B, hρ⟩ : ∃ B, HasParam σ J L h ρ B)

theorem HasParam.paramOf_eq_of_isSplit (hv : IsSplit (E := E) v) (hρ : HasParam σ J L h ρ B) :
    paramOf σ J L h ρ = B := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact (hρ.hasParam_paramOf.isParamVec hx.mem_fixed hx.ne_zero).unique_of_isSplit hv hx

theorem hasParam_psFunGL (hv : IsSplit (E := E) v) {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)}
    (he : IsSplitChart σ J L h e) (α : Fin n → ℂˣ) :
    HasParam σ J L h ((psFunGL w α).comp e.toMonoidHom) (Finset.univ.val.map α) := by
  refine Or.inl ⟨hv, e, he, ?_⟩
  convert hasSatGL_psFunGL (w := w) α using 1
  exact MonoidHom.ext fun g => congrArg (psFunGL w α) (e.apply_symm_apply g)

end Param

section Global

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  (S : Set (HeightOneSpectrum (𝓞 F))) {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]

def HasParamOff (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)) (c : Fam E) : Prop :=
  ∀ v ∉ S, ∀ (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), HasParam σ J L h (π v) (c w)

def HasParamOffFin (ρ : Representation ℂ (GFin σ J) V) (c : Fam E) : Prop :=
  HasParamOff σ J L S (Vl := fun _ => V) (fun v => ρ.comp (embLocFin σ J v)) c

def HasParamOffAd (ρ : Representation ℂ (GAd σ J) V) (c : Fam E) : Prop :=
  HasParamOff σ J L S (Vl := fun _ => V) (fun v => ρ.comp (emb σ J v)) c

def IsParamVecOff (ρ : Representation ℂ (GAd σ J) V) (x : V) (c : Fam E) : Prop :=
  ∀ v ∉ S, ∀ (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v),
    IsParamVec σ J L h (ρ.comp (emb σ J v)) x (c w)

def IsParamFun (f : GAd σ J → V) (c : Fam E) : Prop := IsParamVecOff σ J L S (rightReg ℂ _ V) f c

variable (n) in

def IsSysParamOff (c : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ) (B : Fam E) : Prop :=
  ∀ v ∉ S, ∀ (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSysParam σ n h (c w) (B w)

def paramFam (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)) : Fam E :=
  fun w => paramOf σ J L (rfl : w.under (𝓞 F) = _) (π _)

def LvRep (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)) (m : HeightOneSpectrum (𝓞 E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ := LvTw (paramFam σ J L π) m v s

def LSRep (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) : ℂ :=
  LSTw S (paramFam σ J L π) m s

variable {σ J L S}

theorem HasParamOff.paramFam {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c : Fam E}
    (h : HasParamOff σ J L S π c) : HasParamOff σ J L S π (paramFam σ J L π) := fun v hv w e => by
  subst e; exact (h _ hv w rfl).hasParam_paramOf

theorem HasParamOff.card {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c : Fam E}
    (h : HasParamOff σ J L S π c) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ above E S) : (c w).card = n := by
  obtain ⟨x, hx⟩ := (h _ hw w rfl).exists_vec
  exact hx.card

end Global

section Characters

open Formalism.L2.Host (HChar IsUnitAt IsUnifAt atFin unif)

variable (F E) in

def IsHecke (χ : (AF F ⊗[F] E)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1

variable (F) in

def IsHeckeF (χ : (AF F)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ a : Fˣ, χ (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1

variable (F E) in

def ideleMap : (AF F)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom

variable (F E) in

def IsEta (η : (AF F)ˣ →* Circle) : Prop :=
  Continuous η ∧ (∀ a : Fˣ, η (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) ∧
    (∀ x : (AF F ⊗[F] E)ˣ, η (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) x) = 1) ∧ η ≠ 1

variable (F E) in

def ResEta (χ : (AF F ⊗[F] E)ˣ →* Circle) (k : ℕ) : Prop :=
  AllSome (IsEta F E) fun η => ∀ a, χ (ideleMap F E a) = η a ^ k

def toHChar (χ : (AF F)ˣ →* Circle) (h : IsHeckeF F χ) : HChar F :=
  ⟨Circle.toUnits.comp χ, Units.continuous_iff.2 ⟨continuous_subtype_val.comp h.1,
    (continuous_subtype_val.comp h.1.inv).congr fun x => Circle.coe_inv (χ x)⟩, fun k => (congrArg Circle.toUnits (h.2 k)).trans (map_one _)⟩

theorem isUnitary_toHChar (χ : (AF F)ˣ →* Circle) (h : IsHeckeF F χ) : (toHChar χ h).IsUnitary :=
  fun x => Circle.norm_coe (χ x)

theorem IsEta.isHeckeF {η : (AF F)ˣ →* Circle} (h : IsEta F E η) : IsHeckeF F η := ⟨h.1, h.2.1⟩

variable (F E) in

def toFinAd : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E :=
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨GlobalTheory.AdeleBaseChange.adMap F E, GlobalTheory.AdeleBaseChange.adMap_algebraMap⟩ : Af F →ₐ[F] FiniteAdeleRing (𝓞 E) E)
    (⟨algebraMap E _, fun _ => rfl⟩ : E →ₐ[F] FiniteAdeleRing (𝓞 E) E)).toRingHom

theorem toFinAd_tmul (a : Af F) (x : E) :
    toFinAd F E (a ⊗ₜ[F] x) = GlobalTheory.AdeleBaseChange.adMap F E a * algebraMap E _ x := rfl

theorem toFinAd_bijective : Function.Bijective (toFinAd F E) := by
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have h : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  exact (Function.Bijective.of_comp_iff _ c.bijective).1
    ⟨GlobalTheory.AdeleBaseChange.map_injective h, GlobalTheory.AdeleBaseChange.map_surjective h⟩

variable (F E) in

def finAdEquiv : Af F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E := RingEquiv.ofBijective _ toFinAd_bijective

theorem finAdEquiv_apply {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (y : Af F ⊗[F] E) : finAdEquiv F E y w =
      toCompl h (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) y) := by
  subst h
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ← ha, ← hb]; rfl

variable (F E) in

def extZero : Af F ⊗[F] E →ₙ+* AF F ⊗[F] E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) fun _ _ => Prod.ext (mul_zero _).symm rfl

variable (F E) in

def ofFinIdele : (Af F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ :=
  Units.map
    { toFun := fun y => 1 - extZero F E 1 + extZero F E y
      map_one' := sub_add_cancel _ _
      map_mul' := fun a b => by
        have h1 := map_mul (extZero F E) 1 1
        have h2 := map_mul (extZero F E) a 1
        have h3 := map_mul (extZero F E) 1 b
        rw [mul_one] at h1 h2
        rw [one_mul] at h3
        rw [map_mul]
        linear_combination h1 - h2 - h3 }

variable (F) in

def locIdele (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* (AF F ⊗[F] E)ˣ :=
  (ofFinIdele F E).comp ((Units.map (finAdEquiv F E).symm.toRingHom.toMonoidHom).comp (GlobalTheory.CMVal.single w))

variable (χ ψ : (AF F ⊗[F] E)ˣ →* Circle) (w : HeightOneSpectrum (𝓞 E))

def locChar : (w.adicCompletion E)ˣ →* ℂˣ := Circle.toUnits.comp (χ.comp (locIdele F w))

def UnrAt : Prop := ∀ x, IsUnitAt w x → locChar χ w x = 1

def UnrOff (S : Set (HeightOneSpectrum (𝓞 F))) : Prop := ∀ w ∉ above E S, UnrAt χ w

def val : ℂˣ := locChar χ w (atFin w (unif w))

open Classical in

def charFam : Fam E := fun w => if UnrAt χ w then {val χ w} else 0

def charL (S : Set (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ := LS S (charFam χ) s

@[simp] theorem val_mul : val (χ * ψ) w = val χ w * val ψ w := map_mul Circle.toUnits _ _
@[simp] theorem val_inv : val χ⁻¹ w = (val χ w)⁻¹ := map_inv Circle.toUnits _
@[simp] theorem val_one : val (1 : (AF F ⊗[F] E)ˣ →* Circle) w = 1 := map_one Circle.toUnits
theorem norm_locChar (x : (w.adicCompletion E)ˣ) : ‖(locChar χ w x : ℂ)‖ = 1 := Circle.norm_coe _
theorem norm_val : ‖(val χ w : ℂ)‖ = 1 := norm_locChar χ w _

variable {χ ψ w}

theorem UnrAt.mul (h : UnrAt χ w) (h' : UnrAt ψ w) : UnrAt (χ * ψ) w := fun x hx =>
  (map_mul Circle.toUnits _ _).trans (show locChar χ w x * locChar ψ w x = 1 by rw [h x hx, h' x hx, one_mul])

theorem UnrAt.inv (h : UnrAt χ w) : UnrAt χ⁻¹ w := fun x hx =>
  (map_inv Circle.toUnits _).trans (inv_eq_one.2 (h x hx))

theorem UnrAt.locChar_eq_val (h : UnrAt χ w) {x : (w.adicCompletion E)ˣ} (hx : IsUnifAt w x) :
    locChar χ w x = val χ w := by
  have h1 : IsUnitAt w (x * (atFin w (unif w))⁻¹) := by
    have := Formalism.L2.Host.unif_spec w
    unfold IsUnifAt at hx this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, this, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have := h _ h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

theorem charFam_of_unrAt (h : UnrAt χ w) : charFam χ w = {val χ w} := if_pos h

theorem bounded_charFam (T : Set (HeightOneSpectrum (𝓞 E))) (χ : (AF F ⊗[F] E)ˣ →* Circle) :
    Bounded T (charFam χ) 1 0 := fun w _ => by
  unfold charFam
  split_ifs
  · refine ⟨by simp, fun b hb => ?_⟩
    rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, norm_val]
  · simp

theorem converges_charFam (T : Set (HeightOneSpectrum (𝓞 E))) (χ : (AF F ⊗[F] E)ˣ →* Circle) {s : ℂ}
    (hs : 1 < s.re) : Converges T (charFam χ) s := (bounded_charFam T χ).converges (by simpa using hs)

theorem Bounded.converges_twist_val {T : Set (HeightOneSpectrum (𝓞 E))} {c : Fam E} {r : ℕ} {κ : ℝ}
    (h : Bounded T c r κ) (μ : (AF F ⊗[F] E)ˣ →* Circle) {s : ℂ} (hs : κ + 1 < s.re) :
    Converges T (LFun.twist c (val μ)⁻¹) s :=
  (h.twist fun w _ => by simp [norm_val]).converges hs

end Characters

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHeckeChar_iff (χ : (AE D)ˣ →* Circle) : IsHeckeChar D χ ↔ IsHecke D.host.F D.host.E χ := Iff.rfl
theorem resEta_iff (χ : (AE D)ˣ →* Circle) (k : ℕ) :
    Formalism.L2.Theta.ResEta D χ k ↔ ResEta D.host.F D.host.E χ k := Iff.rfl

variable (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))

abbrev IsParamFunV {X : Type} [AddCommGroup X] [Module ℂ X] (f : GA D V → X) (c : Fam D.host.E) : Prop :=
  IsParamFun D.sp.cm.sig V.gram (frameLat V) (S : Set _) f c

abbrev HasParamOffV {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GA D V) X)
    (c : Fam D.host.E) : Prop :=
  HasParamOffAd D.sp.cm.sig V.gram (frameLat V) (S : Set _) ρ c

variable (D) in

abbrev IsSysParamD (n : ℕ) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (B : Fam D.host.E) : Prop :=
  IsSysParamOff D.sp.cm.sig n (S : Set _) c B

variable (D) in

abbrev LSD (c : Fam D.host.E) (μ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ := LSTw (F := D.host.F) (S : Set _) c (val μ) s

end Record

example (S : Set (HeightOneSpectrum (𝓞 F))) (s : ℂ) :
    charL (1 : (AF F ⊗[F] E)ˣ →* Circle) S s = zetaOff (above E S) s := by
  have : charFam (1 : (AF F ⊗[F] E)ˣ →* Circle) = fun _ => {1} :=
    funext fun w => (charFam_of_unrAt (χ := 1) fun _ _ => map_one Circle.toUnits).trans (by simp)
  rw [charL, this, LS, zetaOff]

example (μ : (AF F ⊗[F] E)ˣ →* Circle) : twist (fun w => {val μ w}) (val μ)⁻¹ = fun _ => {1} := by
  funext w; simp [twist]

end GlobalTheory.LFun

end
