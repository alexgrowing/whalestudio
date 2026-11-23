import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

@[simp] theorem RU_apply (x g : UA E n) (φ : UA E n → ℂ) : RU E n x φ g = φ (g * x) := rfl

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

instance : (finU E n).Normal := MonoidHom.normal_ker _

instance : (infU E n).Normal := MonoidHom.normal_ker _

theorem fin_mul_inf {k x : UA E n} (hk : k ∈ finU E n) (hx : x ∈ infU E n) : k * x = x * k := by
  have h1 : GeneralLinearGroup.map (pInf E) k.1 = 1 := hk
  have h2 : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]

variable (E n) in

def autU : Submodule ℂ (UA E n → ℂ) where
  carrier := {φ | IsAutFormU φ}
  add_mem' {a b} ha hb := by
    refine ⟨ha.cont.add hb.cont, fun γ hγ g => by simp [ha.left γ hγ g, hb.left γ hγ g],
      (smoothPart ((RU E n).comp (finU E n).subtype)).add_mem ha.level hb.level, ?_⟩
    have := ha.kfin
    have := hb.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k a) ⊔
      Submodule.span ℂ (Set.range fun k : infU E n => RU E n k b)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  zero_mem' := by
    refine ⟨continuous_const, fun _ _ _ => rfl, (smoothPart ((RU E n).comp (finU E n).subtype)).zero_mem, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact map_zero (RU E n k)
  smul_mem' c {a} ha := by
    refine ⟨ha.cont.const_smul c, fun γ hγ g => by simp [ha.left γ hγ g],
      (smoothPart ((RU E n).comp (finU E n).subtype)).smul_mem c ha.level, ?_⟩
    have := ha.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)

theorem mem_autU {φ : UA E n → ℂ} : φ ∈ autU E n ↔ IsAutFormU φ := Iff.rfl

theorem smooth_normal {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) [hN : N.Normal] (x : G) {v : V} (h : IsOpen {k : N | ρ k v = v}) :
    IsOpen {k : N | ρ k (ρ x v) = ρ x v} := by
  let c : N → N := fun k => ⟨x⁻¹ * k * x, hN.conj_mem' _ k.2 x⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  convert h.preimage hc using 1
  ext k
  change ρ k (ρ x v) = ρ x v ↔ ρ (x⁻¹ * k * x) v = v
  have hm : ∀ a b u, ρ a (ρ b u) = ρ (a * b) u := fun a b u => by rw [map_mul]; rfl
  constructor
  · intro e
    rw [mul_assoc, ← hm, ← hm, e, hm, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro e
    conv_rhs => rw [← e]
    rw [hm, hm, mul_assoc, mul_inv_cancel_left]

theorem RU_mem_autU (x : UA E n) (φ : UA E n → ℂ) (h : φ ∈ autU E n) : RU E n x φ ∈ autU E n := by
  refine ⟨h.cont.comp (continuous_mul_const x), fun γ hγ g => ?_, ?_, ?_⟩
  · rw [RU_apply, RU_apply, mul_assoc, h.left γ hγ]
  · exact smooth_normal (RU E n) (finU E n) x h.level
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (RU E n x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨x⁻¹ * k * x, Subgroup.Normal.conj_mem' inferInstance _ k.2 x⟩, rfl⟩, ?_⟩
    simp only [RU_RU, mul_assoc, mul_inv_cancel_left]

variable (E n) in

def autRep : Representation ℂ (UA E n) (autU E n) := sub (RU E n) (autU E n) RU_mem_autU

variable (E n) in

abbrev Wt : Type := InfinitePlace E → DomWeight n

def zeroWt (n : ℕ) : DomWeight n := ⟨0, antitone_const⟩

theorem dual_dual (lam : DomWeight n) : lam.dual.dual = lam := by
  cases lam
  simp [DomWeight.dual]

open Classical in

def Wt.at (W : Wt E n) (τ : E →+* ℂ) : DomWeight n :=
  if (InfinitePlace.mk τ).embedding = τ then W (InfinitePlace.mk τ) else (W (InfinitePlace.mk τ)).dual

omit [NumberField E] [IsCMField E] in

@[simp] theorem Wt.at_embedding (W : Wt E n) (v : InfinitePlace E) : W.at v.embedding = W v := by
  simp [Wt.at]

theorem conjugate_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))

theorem Wt.at_conjugate (W : Wt E n) (τ : E →+* ℂ) : W.at (ComplexEmbedding.conjugate τ) = (W.at τ).dual := by
  unfold Wt.at
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact (conjugate_ne τ).symm)]
  · rw [if_pos h, if_neg (by rw [h]; exact conjugate_ne τ), dual_dual]

omit [NumberField E] [IsCMField E] in

theorem Wt.at_injective : Function.Injective (Wt.at : Wt E n → _) := fun W W' h =>
  funext fun v => by rw [← W.at_embedding, h, W'.at_embedding]

def Wt.ofFam (lam : (E →+* ℂ) → DomWeight n) : Wt E n := fun v => lam v.embedding

theorem Wt.at_ofFam {lam : (E →+* ℂ) → DomWeight n} (h : ∀ τ, lam (ComplexEmbedding.conjugate τ) = (lam τ).dual)
    (τ : E →+* ℂ) : (Wt.ofFam lam).at τ = lam τ := by
  unfold Wt.at Wt.ofFam
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [if_pos e, e]
  · rw [if_neg (by rw [e]; exact conjugate_ne τ), e, h, dual_dual]

def infW (W : Wt E n) (τ : E →+* ℂ) : Multiset ℂ := infOfWeight (W.at τ)

omit [NumberField E] [IsCMField E] in

theorem infW_card (W : Wt E n) (τ : E →+* ℂ) : Multiset.card (infW W τ) = n := by
  simp [infW, infOfWeight]

omit [NumberField E] [IsCMField E] in

theorem infW_alg (W : Wt E n) (τ : E →+* ℂ) :
    (infW W τ).Nodup ∧ ∀ x ∈ infW W τ, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨GlobalTheory.DefiniteBC.nodup_infOfWeight _, fun x hx => ?_⟩
  rw [infW, infOfWeight, Multiset.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact ⟨(W.at τ).w k - (k : ℕ), by push_cast; ring⟩

theorem infW_conjugate (W : Wt E n) (τ : E →+* ℂ) :
    infW W (ComplexEmbedding.conjugate τ) = (infW W τ).map fun z => -z := by
  rw [infW, W.at_conjugate, GlobalTheory.DefiniteBC.infOfWeight_dual, infW]

def cAll : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) := MonoidHom.pi fun v => cEmb v.embedding

abbrev Wt.Sp (W : Wt E n) : Type := Formalism.L2.DIV.VV ℂ (ι := InfinitePlace E) W

def Wt.rep (W : Wt E n) : Representation ℂ (infU E n) W.Sp :=
  (Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (cAll.comp (infU E n).subtype)

instance (W : Wt E n) : FiniteDimensional ℂ W.Sp :=
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (W v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ W)

def algForms (W : Wt E n) : Submodule ℂ (W.Sp →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (W.rep x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

def postRep (W : Wt E n) : Representation ℂ (finU E n) (W.Sp →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

@[simp] theorem postRep_apply (W : Wt E n) (k : finU E n) (f : W.Sp →ₗ[ℂ] (UA E n → ℂ)) (v : W.Sp) :
    postRep W k f v = RU E n k (f v) := rfl

theorem postRep_mem (W : Wt E n) (k : finU E n) (f : W.Sp →ₗ[ℂ] (UA E n → ℂ)) (h : f ∈ algForms W) :
    postRep W k f ∈ algForms W :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [postRep_apply, postRep_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def algRep (W : Wt E n) : Representation ℂ (finU E n) (algForms W) := sub (postRep W) (algForms W) (postRep_mem W)

theorem isSmooth_algRep (W : Wt E n) : IsSmooth (algRep W) := fun f => by
  let b := Module.finBasis ℂ W.Sp
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

def algForms.val {W : Wt E n} (f : algForms W) (g : UA E n) : Module.Dual ℂ W.Sp := (LinearMap.proj g).comp f.1

theorem algForms.val_left {W : Wt E n} (f : algForms W) {γ : UA E n} (hγ : γ ∈ ratU E n) (g : UA E n) :
    algForms.val f (γ * g) = algForms.val f g := LinearMap.ext fun v => (f.2.1 v).left γ hγ g

theorem algForms.val_right {W : Wt E n} (f : algForms W) (g : UA E n) (x : infU E n) :
    algForms.val f (g * x) = W.rep.dual x⁻¹ (algForms.val f g) := LinearMap.ext fun v => by
  rw [Representation.dual_apply, inv_inv]
  exact (congrFun (f.2.2 x v) g).symm

theorem algForms.val_algRep {W : Wt E n} (f : algForms W) (k : finU E n) (g : UA E n) :
    algForms.val (algRep W k f) g = algForms.val f (g * k) := rfl

variable (E n) in

@[ext] structure AutSub where

  V : Submodule ℂ (UA E n → ℂ)
  isAut : IsAutRepU V

namespace AutSub

variable (π π' : AutSub E n)

def rep : Representation ℂ (UA E n) π.V := sub (RU E n) π.V π.isAut.stable

@[simp] theorem rep_val (x : UA E n) (φ : π.V) : (π.rep x φ).1 = RU E n x φ.1 := rfl

theorem le_autU : π.V ≤ autU E n := π.isAut.aut

theorem isIrreducible_rep : π.rep.IsIrreducible := by
  refine (CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot, fun W hW => ?_⟩
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  refine (π.isAut.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp
    (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans (Submodule.map_subtype_top _).symm)
  rintro x _ ⟨φ, hφ, rfl⟩
  exact ⟨_, hW x φ hφ, rfl⟩

def Iso : Prop := Nonempty (π.rep.Equiv π'.rep)

variable (E n) in

instance setoid : Setoid (AutSub E n) where
  r := Iso
  iseqv := ⟨fun π => ⟨.refl π.rep⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

def incl : π.rep.IntertwiningMap (autRep E n) := ⟨Submodule.inclusion π.le_autU, fun _ => rfl⟩

theorem incl_ne_zero : π.incl ≠ 0 := fun h => π.isAut.ne_bot <| (Submodule.eq_bot_iff _).2 fun φ hφ =>
  (congrArg Subtype.val (DFunLike.congr_fun h ⟨φ, hφ⟩) :)

def mult : ℕ := Module.finrank ℂ (π.rep.IntertwiningMap (autRep E n))

theorem mult_pos [FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n))] : 0 < π.mult :=
  Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, π.incl_ne_zero⟩

def finPart (W : Wt E n) : Submodule ℂ (algForms W) :=
  ⨅ v : W.Sp, π.V.comap ((LinearMap.applyₗ v).comp (algForms W).subtype)

variable {π} in

theorem mem_finPart {W : Wt E n} {f : algForms W} : f ∈ π.finPart W ↔ ∀ v, f.1 v ∈ π.V := Submodule.mem_iInf _

def finRep (W : Wt E n) : Representation ℂ (finU E n) (π.finPart W) :=
  sub (algRep W) (π.finPart W) fun k _ h => mem_finPart.2 fun v => π.isAut.stable k _ (mem_finPart.1 h v)

theorem isSmooth_finRep (W : Wt E n) : IsSmooth (π.finRep W) := fun f => by
  convert isSmooth_algRep W f.1 using 1
  ext k
  exact Subtype.ext_iff

def IsLocComp (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  IsCompAlong π.V (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ

def IsSat (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s q ∧ HasSatAt π.V w s ϖ q α

variable {π π'}

theorem Iso.exists_map (h : Iso π π') : ∃ T : π.V →ₗ[ℂ] (UA E n → ℂ), Function.Injective T ∧ (∀ φ, T φ ∈ π'.V) ∧
    ∀ x φ, T (π.rep x φ) = RU E n x (T φ) := by
  obtain ⟨e⟩ := h
  exact ⟨π'.V.subtype ∘ₗ e.toLinearMap, Subtype.val_injective.comp e.toLinearEquiv.injective, fun φ => (e φ).2,
    fun x φ => congrArg Subtype.val (LinearMap.congr_fun (e.isIntertwining' x) φ)⟩

theorem Iso.isCompAlong (h : Iso π π') {Gv : Subgroup (UA E n)} {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
    {p : Gv →* H} {σ : Representation ℂ H W} (hσ : IsCompAlong π.V Gv p σ) : IsCompAlong π'.V Gv p σ := by
  obtain ⟨T, hi, hm, hT⟩ := h.exists_map
  obtain ⟨h1, f, h0, hf, h2⟩ := hσ
  refine ⟨h1, T ∘ₗ f.codRestrict _ hf, fun e => h0 (LinearMap.ext fun v => ?_), fun v => hm _, fun x v => ?_⟩
  · exact congrArg Subtype.val (hi ((LinearMap.congr_fun e v).trans (map_zero T).symm))
  · exact (congrArg T (Subtype.ext (h2 x v))).trans (hT x ⟨f v, hf v⟩)

theorem Iso.isUnramU (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} (hw : IsUnramU π.V w) : IsUnramU π'.V w := by
  obtain ⟨T, hi, hm, hT⟩ := h.exists_map
  obtain ⟨φ, hφ, h0, h1⟩ := hw
  refine ⟨T ⟨φ, hφ⟩, hm _, fun e => h0 (congrArg Subtype.val (hi (e.trans (map_zero T).symm))), fun x hx hk => ?_⟩
  rw [← hT]
  exact congrArg T (Subtype.ext (h1 x hx hk))

theorem Iso.isSat (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} {α : Fin (n / 2) → ℂˣ} (hα : π.IsSat w α) :
    π'.IsSat w α := by
  obtain ⟨s, ϖ, q, h1, h2, b, hb, h3, p, hp, σ, h4, h5⟩ := hα
  exact ⟨s, ϖ, q, h1, h2, b, hb, h3, p, hp, σ, h.isCompAlong h4, h5⟩

theorem Iso.mult_eq (h : Iso π π') : π.mult = π'.mult := by
  obtain ⟨e⟩ := h
  refine LinearEquiv.finrank_eq
    { toFun := fun f => f.comp e.symm.toIntertwiningMap
      invFun := fun f => f.comp e.toIntertwiningMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => DFunLike.ext _ _ fun v => congrArg f (e.symm_apply_apply v)
      right_inv := fun f => DFunLike.ext _ _ fun v => congrArg f (e.apply_symm_apply v) }

theorem IsLocComp.congr {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) (hπ : Iso π π') (hσ : Nonempty (σ.ρ.Equiv σ'.ρ)) : π'.IsLocComp w σ' := by
  obtain ⟨-, f, h0, hf, h2⟩ := hπ.isCompAlong h
  obtain ⟨e⟩ := hσ
  refine ⟨σ'.irred, f ∘ₗ e.symm.toLinearMap, fun h => h0 (LinearMap.ext fun v => ?_), fun v => hf _, fun x v => ?_⟩
  · exact (congrArg f (e.symm_apply_apply v)).symm.trans (LinearMap.congr_fun h (e v))
  · exact (congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' _) v)).trans (h2 x _)

end AutSub

def detChar (n : ℕ) (χ : Formalism.L2.Host.HChar E) : UA E n →* ℂˣ := (chiDet n χ).comp (UA E n).subtype

def detFn (n : ℕ) (χ : Formalism.L2.Host.HChar E) : UA E n → ℂ := fun g => detChar n χ g

theorem RU_detFn (χ : Formalism.L2.Host.HChar E) (x : UA E n) : RU E n x (detFn n χ) = (detChar n χ x : ℂ) • detFn n χ := by
  funext g
  simp [detFn, mul_comm]

theorem detFn_ne_zero (χ : Formalism.L2.Host.HChar E) : detFn n χ ≠ 0 := fun h => (detChar n χ 1).ne_zero (congrFun h 1)

omit [IsCMField E] in

theorem continuous_map_pFin : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem detFn_mem (χ : Formalism.L2.Host.HChar E) : detFn n χ ∈ autU E n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Units.continuous_val.comp (χ.2.1.comp ((GeneralLinearGroup.continuous_det (n := Fin n)).comp
      continuous_subtype_val))
  · rintro γ ⟨δ, hδ⟩ g
    have : detChar n χ γ = 1 := (congrArg (chiDet n χ) hδ.symm).trans (chiDet_ratGL χ δ)
    simp [detFn, this]
  · have hc : Continuous fun k : finU E n => GeneralLinearGroup.map (pFin E) k.1.1 :=
      continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
    have ho := (isOpen_ker_chiDet (a := n) χ).preimage hc
    have h0 : chiDet n χ (finGL E n (GeneralLinearGroup.map (pFin E) (1 : finU E n).1.1)) = 1 :=
      ((chiDet n χ).comp ((finGL E n).comp (GeneralLinearGroup.map (pFin E)))).map_one
    refine isOpen_stab_of_mem_nhds ((RU E n).comp (finU E n).subtype) (detFn n χ) ?_
    refine Filter.mem_of_superset (ho.mem_nhds h0) fun k hk => ?_
    have h1 : finGL E n (GeneralLinearGroup.map (pFin E) k.1.1) = k.1.1 :=
      ga_ext (by rw [pInf_finGL]; exact (MonoidHom.mem_ker.1 k.2).symm) (pFin_finGL _)
    have h2 : detChar n χ k = 1 := (congrArg (chiDet n χ) h1.symm).trans hk
    change RU E n k (detFn n χ) = _
    rw [RU_detFn, h2, Units.val_one, one_smul]
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {detFn n χ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨(detChar n χ k.1 : ℂˣ), (RU_detFn χ k.1).symm⟩

variable (n) in

def AutSub.ofChar (χ : Formalism.L2.Host.HChar E) : AutSub E n where
  V := Submodule.span ℂ {detFn n χ}
  isAut := ⟨fun _ h => (Submodule.span_singleton_le_iff_mem _ _).2 (detFn_mem χ) h, fun x φ h => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h
      rw [map_smul, RU_detFn]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
    fun h => detFn_ne_zero χ (Submodule.span_singleton_eq_bot.1 h),
    fun _ hW _ => (nonzero_span_atom _ (detFn_ne_zero χ)).le_iff.1 hW⟩

theorem AutSub.rep_ofChar (χ : Formalism.L2.Host.HChar E) (x : UA E n) (φ : (AutSub.ofChar n χ).V) :
    (AutSub.ofChar n χ).rep x φ = (detChar n χ x : ℂ) • φ := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 φ.2
  refine Subtype.ext ?_
  change RU E n x φ.1 = _ • φ.1
  rw [← hc, map_smul, RU_detFn, smul_comm]

variable (E n) in

def AutSub.triv : AutSub E n := ⟨Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}, isAutRepU_const⟩

theorem AutSub.mult_ofChar (χ : Formalism.L2.Host.HChar E) : (AutSub.ofChar n χ).mult = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' _ (AutSub.ofChar n χ).incl_ne_zero).2 fun f => ?_
  let e : (AutSub.ofChar n χ).V := ⟨detFn n χ, Submodule.mem_span_singleton_self _⟩
  have h1 : (f e).1 = (f e).1 1 • detFn n χ := funext fun g => by
    have h := congrFun (congrArg Subtype.val (f.isIntertwining _ _ g e)) 1
    rw [AutSub.rep_ofChar, map_smul] at h
    have h' : detFn n χ g * (f e).1 1 = (f e).1 (1 * g) := h
    rw [one_mul] at h'
    rw [← h', mul_comm]
    rfl
  refine ⟨(f e).1 1, DFunLike.ext _ _ fun φ => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 φ.2
  obtain rfl : c • e = φ := Subtype.ext hc
  rw [map_smul, map_smul]
  exact congrArg _ (Subtype.ext h1.symm)

variable (E n) in

def AU : Type := Quotient (AutSub.setoid E n)

namespace AU

def mk (π : AutSub E n) : AU E n := Quotient.mk _ π

theorem mk_eq_mk {π π' : AutSub E n} : mk π = mk π' ↔ π.Iso π' := Quotient.eq

theorem mk_surjective : Function.Surjective (mk : AutSub E n → AU E n) := Quotient.mk_surjective

instance : Inhabited (AU E n) := ⟨mk (AutSub.triv E n)⟩

def mult (π : AU E n) : ℕ := Quotient.liftOn π AutSub.mult fun _ _ h => AutSub.Iso.mult_eq h

@[simp] theorem mult_mk (π : AutSub E n) : (mk π).mult = π.mult := rfl

def Sph (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Quotient.liftOn π (fun π => IsUnramU π.V w) fun _ _ h =>
    propext ⟨AutSub.Iso.isUnramU h, AutSub.Iso.isUnramU (Setoid.symm h)⟩

@[simp] theorem sph_mk (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) : (mk π).Sph w ↔ IsUnramU π.V w := Iff.rfl

def IsLoc (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) (σ : Irr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  Quotient.liftOn₂ π σ (fun π σ => π.IsLocComp w σ) fun _ _ _ _ h h' =>
    propext ⟨fun x => x.congr h h', fun x => x.congr (Setoid.symm h) (Setoid.symm h')⟩

@[simp] theorem isLoc_mk (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) :
    (mk π).IsLoc w (Quotient.mk _ σ) ↔ π.IsLocComp w σ := Iff.rfl

def loc (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Irr (GL (Fin n) (w.adicCompletion E)) :=
  Classical.epsilon (π.IsLoc w)

theorem IsLoc.loc {π : AU E n} {w : HeightOneSpectrum (𝓞 E)} {σ : Irr (GL (Fin n) (w.adicCompletion E))}
    (h : π.IsLoc w σ) : π.IsLoc w (π.loc w) := Classical.epsilon_spec ⟨σ, h⟩

def IsSat (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  Quotient.liftOn π (·.IsSat w α) fun _ _ h => propext ⟨AutSub.Iso.isSat h, AutSub.Iso.isSat (Setoid.symm h)⟩

@[simp] theorem isSat_mk (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) :
    (mk π).IsSat w α ↔ π.IsSat w α := Iff.rfl

def satVec (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Fin (n / 2) → ℂˣ := Classical.epsilon (π.IsSat w)

theorem IsSat.satVec {π : AU E n} {w : HeightOneSpectrum (𝓞 E)} {α : Fin (n / 2) → ℂˣ} (h : π.IsSat w α) :
    π.IsSat w (π.satVec w) := Classical.epsilon_spec ⟨α, h⟩

def sat (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂ := Finset.univ.val.map fun i => (π.satVec w i : ℂ)

theorem sat_card (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Multiset.card (π.sat w) = n / 2 := by
  simp [sat]

theorem zero_notMem_sat (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : (0 : ℂ) ∉ π.sat w := fun h => by
  obtain ⟨i, -, e⟩ := Multiset.mem_map.1 h
  exact (π.satVec w i).ne_zero e

def HasWt (π : AU E n) (τ : E →+* ℂ) (lam : DomWeight n) : Prop :=
  Quotient.liftOn π (fun π => HasWeightAt π.V τ lam) fun _ _ h =>
    propext ⟨AutSub.Iso.isCompAlong h, AutSub.Iso.isCompAlong (Setoid.symm h)⟩

@[simp] theorem hasWt_mk (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n) :
    (mk π).HasWt τ lam ↔ HasWeightAt π.V τ lam := Iff.rfl

theorem HasWt.conjugate {π : AU E n} {τ : E →+* ℂ} {lam : DomWeight n} (h : π.HasWt τ lam) :
    π.HasWt (ComplexEmbedding.conjugate τ) lam.dual := by
  obtain ⟨π, rfl⟩ := mk_surjective π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : lam.dual = lam := by
      cases lam
      unfold DomWeight.dual
      congr 1
      exact Subsingleton.elim _ _
    obtain ⟨hi, f, h0, h1, h2⟩ := h
    rw [e]
    refine ⟨hi, f, h0, h1, fun x v => Eq.trans ?_ (h2 ⟨x.1, GlobalTheory.DefiniteBC.embU_conjugate τ ▸ x.2⟩ v)⟩
    exact congrArg (fun g => f (GlobalTheory.Branching.sqRep ℂ 0 lam g v)) (Subsingleton.elim _ _)
  · exact GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn h

def wt (π : AU E n) : Wt E n := fun v => @Classical.epsilon _ ⟨zeroWt n⟩ (π.HasWt v.embedding)

theorem HasWt.wt {π : AU E n} {τ : E →+* ℂ} {lam : DomWeight n} (h : π.HasWt τ lam) : π.HasWt τ (π.wt.at τ) := by
  have key : ∀ (v : InfinitePlace E) (mu : DomWeight n), π.HasWt v.embedding mu → π.HasWt v.embedding (π.wt v) :=
    fun v mu hmu => Classical.epsilon_spec (p := π.HasWt v.embedding) ⟨mu, hmu⟩
  unfold Wt.at
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · have := key (InfinitePlace.mk τ) lam (by rw [e]; exact h)
    rw [e] at this
    rwa [if_pos e]
  · have := (key (InfinitePlace.mk τ) lam.dual (by rw [e]; exact h.conjugate)).conjugate
    rw [e, ComplexEmbedding.involutive_conjugate E τ] at this
    rwa [if_neg (by rw [e]; exact conjugate_ne τ)]

def ofChar (n : ℕ) (χ : Formalism.L2.Host.HChar E) : AU E n := mk (AutSub.ofChar n χ)

theorem ofChar_eq_iff {χ χ' : Formalism.L2.Host.HChar E} : ofChar n χ = ofChar n χ' ↔ detChar n χ = detChar n χ' := by
  constructor
  · intro h
    obtain ⟨e⟩ := mk_eq_mk.1 h
    have := Submodule.nontrivial_iff_ne_bot.2 (AutSub.ofChar n χ).isAut.ne_bot
    obtain ⟨φ, hφ⟩ := exists_ne (0 : (AutSub.ofChar n χ).V)
    ext x
    have h1 : e ((AutSub.ofChar n χ).rep x φ) = (AutSub.ofChar n χ').rep x (e φ) :=
      LinearMap.congr_fun (e.isIntertwining' x) φ
    rw [AutSub.rep_ofChar, AutSub.rep_ofChar, map_smul] at h1
    exact smul_left_injective ℂ ((map_ne_zero_iff e e.injective).2 hφ) h1
  · intro h
    refine congrArg mk (AutSub.ext ?_)
    change Submodule.span ℂ {detFn n χ} = Submodule.span ℂ {detFn n χ'}
    unfold detFn
    rw [h]

theorem mult_ofChar (χ : Formalism.L2.Host.HChar E) : (ofChar n χ).mult = 1 := AutSub.mult_ofChar χ

theorem ofChar_one : ofChar n (1 : Formalism.L2.Host.HChar E) = mk (AutSub.triv E n) := rfl

theorem sph_triv (w : HeightOneSpectrum (𝓞 E)) : (mk (AutSub.triv E n)).Sph w := isUnramU_const w

theorem isLoc_triv (w : HeightOneSpectrum (𝓞 E)) : (mk (AutSub.triv E n)).IsLoc w (Quotient.mk _ (SmIrr.triv _)) :=
  isCompAlong_const _ _ (.refl _)

theorem infW_wt_triv (τ : E →+* ℂ) : infW (mk (AutSub.triv E 1)).wt τ = {0} := by
  have h := weight_eq_zero_of_const τ _ (HasWt.wt (π := mk (AutSub.triv E 1)) (hasWeightAt_const τ))
  simp [infW, infOfWeight, h]

theorem hasWt_ofChar_one (χ : Formalism.L2.Host.HChar E) (τ : E →+* ℂ) (lam : DomWeight 1)
    (h : ∀ x ∈ embU 1 τ, (detChar 1 χ x : ℂ) = cEmb τ x 0 0 ^ lam.w 0) : (ofChar 1 χ).HasWt τ lam := by
  have h0 : GlobalTheory.Branching.RankTwo.one' lam ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  let e : ℂ ≃ₗ[ℂ] nablaSq ℂ 1 lam := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ _ (GlobalTheory.Branching.RankTwo.one' lam))
    ⟨smul_left_injective ℂ h0, fun f => ⟨_, (GlobalTheory.Branching.RankTwo.eq_smul_one lam f).symm⟩⟩
  have : IsSimpleModule ℂ (nablaSq ℂ 1 lam) := IsSimpleModule.congr e.symm
  refine ⟨(CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩,
    e.symm.toLinearMap.smulRight (detFn 1 χ), fun h1 => detFn_ne_zero (n := 1) χ ?_,
    fun v => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun x v => ?_⟩
  · simpa using LinearMap.congr_fun h1 (e 1)
  · rw [GlobalTheory.Branching.RankTwo.small_act, map_smul, LinearMap.smulRight_apply, map_smul, RU_detFn, h x x.2, smul_comm]
    rfl

end AU

example (τ : E →+* ℂ) : infW (Wt.ofFam fun _ => zeroWt 2) τ = {1 / 2, -1 / 2} := by
  rw [infW, Wt.at_ofFam fun _ => by simp [zeroWt, DomWeight.dual]; rfl]
  simp [infOfWeight, zeroWt]
  norm_num
  rfl

theorem finPart_triv_ne_bot : (AutSub.triv E n).finPart (fun _ => zeroWt n) ≠ ⊥ := by
  let W : Wt E n := fun _ => zeroWt n
  let l : W.Sp →ₗ[ℂ] ℂ := (MvPolynomial.aeval (0 : InfinitePlace E × Fin n × Fin n → ℂ)).toLinearMap.comp
    (Submodule.subtype _)
  have hl : ∀ x v, l (W.rep x v) = l v := fun x v => by
    have h1 : ∀ g, Formalism.L2.DIV.detTwK (K := ℂ) W g = 1 := fun g => Finset.prod_eq_one fun τ _ => by
      have : (W τ).detShift = 0 := by simp [W, zeroWt, DomWeight.detShift]
      simp [this, detPow]
    have h2 : ∀ g : InfinitePlace E → GL (Fin n) ℂ, (MvPolynomial.aeval (0 : InfinitePlace E × Fin n × Fin n → ℂ)).comp
        (Formalism.L2.DIV.trAct g) = MvPolynomial.aeval 0 := fun g => MvPolynomial.algHom_ext fun i => by
      simp [Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct]
    change MvPolynomial.aeval 0 (Formalism.L2.DIV.detTwK W (cAll x.1) • Formalism.L2.DIV.trAct (cAll x.1) v.1) = _
    rw [h1, one_smul]
    exact AlgHom.congr_fun (h2 _) v.1
  have h0 : (zeroWt n).natW = 0 := funext fun i => by simp [zeroWt, DomWeight.detShift, DomWeight.natW]
  have h1 : (1 : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) n) ∈ Formalism.L2.DIV.VV ℂ W :=
    Submodule.subset_span ⟨fun _ => 1, fun _ => by
      have := Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl 0 antitone_const
      simpa [nablaSq, W, h0, Formalism.GradedWeylDivisibility.hw] using this, by simp⟩
  have hm : ∀ v, l.smulRight (fun _ => 1 : UA E n → ℂ) v ∈ (AutSub.triv E n).V := fun v =>
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨l.smulRight (fun _ => 1), fun v => (AutSub.triv E n).le_autU (hm v), fun x v => ?_⟩,
    AutSub.mem_finPart.2 hm, fun h => ?_⟩
  · rw [LinearMap.smulRight_apply, hl]
    rfl
  · have := congrFun (LinearMap.congr_fun (congrArg Subtype.val h) ⟨1, h1⟩) 1
    simp [l] at this

section Par

variable {LP : HeightOneSpectrum (𝓞 E) → Type}

def locPar (rc : ∀ w m, SmIrr (GL (Fin m) (w.adicCompletion E)) → LP w) (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : LP w :=
  rc w n (π.loc w).out

theorem locPar_eq {rc : ∀ w m, SmIrr (GL (Fin m) (w.adicCompletion E)) → LP w} {w : HeightOneSpectrum (𝓞 E)}
    (hrc : ∀ σ σ' : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (σ.ρ.Equiv σ'.ρ) → rc w n σ = rc w n σ')
    {π : AU E n} {σ : SmIrr (GL (Fin n) (w.adicCompletion E))} (h : π.loc w = Quotient.mk _ σ) :
    locPar rc π w = rc w n σ :=
  hrc _ _ (Quotient.exact ((Quotient.out_eq _).trans h))

end Par

section Host

open Formalism.MainNotions.N GlobalTheory.DefiniteBC

attribute [local instance] host_isCMField

variable {R : Ranks} (H : Host R)

abbrev HostAU (_j : ℕ) : Type := AU H.E R.nV

abbrev HostWt (_j : ℕ) : Type := Wt H.E R.nV

variable {H} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem isSat_iff {n : ℕ} (π : AutSub H.E n) (w : PlE H) (α : Fin (n / 2) → ℂˣ) : π.IsSat w α ↔ IsSatAt π.V w α :=
  Iff.rfl

def nbc (rc : RecMap A) (emb : ∀ i, A.AV i → HostAU H (N.j i)) (inj : ∀ i, Function.Injective (emb i))
    (loc : ∀ i (P : A.AV i) w, A.locV i P w = locPar rc (emb i P) w)
    (sat : ∀ i (P : A.AV i) w, A.satV i P w = (emb i P).sat w)
    (sph : ∀ i (P : A.AV i) w, ¬ IsSplitPl H w → (emb i P).Sph w)
    (inf : ∀ i (P : A.AV i), A.infWt i = infW (emb i P).wt) : NBC A where
  AU := HostAU H
  multAU _ := AU.mult
  sphAU _ := AU.Sph
  locAU _ := locPar rc
  satAU _ := AU.sat
  satAU_card _ := AU.sat_card
  Wt := HostWt H
  infW _ := infW
  infW_card _ := infW_card
  wtAU _ := AU.wt
  infW_alg _ := infW_alg
  embAV := emb
  embAV_inj := inj
  embAV_loc := loc
  embAV_sat := sat
  embAV_sph := sph
  embAV_inf := inf

theorem unitaryRead_nbc {rc : RecMap A} {emb inj loc sat sph inf}
    (hrc : ∀ w (σ σ' : LocIrr w R.nV), Nonempty (σ.ρ.Equiv σ'.ρ) → rc w R.nV σ = rc w R.nV σ')
    (hloc : ∀ (π : AU H.E R.nV) w σ σ', IsSplitPl H w → π.IsLoc w σ → π.IsLoc w σ' → σ = σ')
    (hsat : ∀ (π : AU H.E R.nV) w, ¬ IsSplitPl H w → π.Sph w → ∃ α, π.IsSat w α)
    (hwt : ∀ (π : AU H.E R.nV) τ, ∃ lam, π.HasWt τ lam) :
    UnitaryRead (nbc rc emb inj loc sat sph inf) rc := by
  intro j _ _ π
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  refine ⟨U.V, U.isAut, fun w hw σ hσ => ?_, fun w hw hs => ?_, fun τ => ?_⟩
  · have h : (AU.mk U).IsLoc w (Quotient.mk _ σ) := hσ
    exact locPar_eq (hrc w) (hloc _ w _ _ hw h.loc h)
  · obtain ⟨α, h⟩ := hsat (AU.mk U) w hw hs
    exact ⟨_, h.satVec, rfl⟩
  · obtain ⟨lam, h⟩ := hwt (AU.mk U) τ
    exact ⟨_, h.wt, rfl⟩

end Host

end GlobalTheory.DefU

end
