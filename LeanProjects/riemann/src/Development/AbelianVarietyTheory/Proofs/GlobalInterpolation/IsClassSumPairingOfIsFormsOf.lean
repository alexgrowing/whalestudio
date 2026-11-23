import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum GlobalTheory.Mem.Col2
open scoped Matrix ComplexOrder

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem Lsh_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E n ∅ SG) : d.1.Lsh = d.1.N := by
  have e : d.1.L = d.1.N := by
    rw [Deco.L]
    simp
  rw [Deco.Lsh, e]
  exact d.2.uni

theorem emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := fun φ => by
  rw [← hX.emb_star]
  exact hX.conjE (φ.comp (X.emb τ)) x

theorem root_mem_cmMax (hX : X.Ok) {c : X.K} (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1) : c ∈ cmMax X.K := fun φ => by
  obtain ⟨m, hm, hc⟩ := hc
  have h1 := star_mul_root hX.conjK hm hc
  have h2 : star (φ c) * φ c = 1 := by
    have h3 : ‖φ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hc, map_one]) hm.ne'
    rw [← starRingEnd_apply, Complex.conj_mul', h3]
    simp
  have h0 : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine mul_right_cancel₀ h0 ?_
  rw [← map_mul, h1, map_one, starRingEnd_apply, h2]

theorem row_act_rat (hX : X.Ok) (g : (mtildeGSD W Ch sel mu P).G) (i j) :
    (mtildeGSD W Ch sel mu P).bV.repr ((mtildeGSD W Ch sel mu P).ρ g ((mtildeGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).1

theorem dual_act_rat (hX : X.Ok) (g : (dualGSD W Ch sel mu P).G) (i j) :
    (dualGSD W Ch sel mu P).bV.repr ((dualGSD W Ch sel mu P).ρ g ((dualGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).2

theorem isFormsOf_MtildeH (hX : X.Ok) : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)
    (MtildeH W Ch hX sel mu P) (LinearEquiv.refl _ _) :=
  isFormsOf_toH _ _ (row_act_rat W Ch sel mu P hX) (fun v => by rw [row_gramV]; exact gramB_posDef _ _) _

def rowPt (c : (stepX Ch sel mu P).Cl) : RowPt Pr R sel mu := toRow sel mu ((stepX Ch sel mu P).rep c).1.1

def rowCl (c : (stepX Ch sel mu P).Cl) : (mtildeGSD W Ch sel mu P).Cl := (mtildeGSD W Ch sel mu P).cls (rowPt Ch sel mu P c)

theorem rowCl_surjective : Function.Surjective (rowCl W Ch sel mu P) := by
  rintro ⟨d⟩
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  refine ⟨(stepX Ch sel mu P).cl () (trivPt X _ _ _ _ p), ?_⟩
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (trivPt X _ _ _ _ p)
  have h1 := congrArg (fun q => toRow sel mu q.1.1) hg
  refine Eq.symm (((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).2 ⟨toRowG Ch sel mu P g, ?_⟩)
  exact (toRow_smul Ch sel mu P g _).symm.trans h1

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

include hd in

theorem exists_step_smul (a : FormG (rowTy Ch sel mu P).inv) (p q : (stepX Ch sel mu P).D ())
    (h : a • toRow sel mu p.1.1 = toRow sel mu q.1.1) :
    ∃ g : (stepX Ch sel mu P).G (), toRowG Ch sel mu P g = a ∧ (letI := (stepX Ch sel mu P).actD (); g • p) = q := by
  obtain ⟨g, h1, h2⟩ := exists_toRowG_smul Ch sel mu P hd a _ _ h
  refine ⟨g, h1, (trivPt X _ _ _ _).symm.injective h2⟩

include hd in
theorem rowCl_injective : Function.Injective (rowCl W Ch sel mu P) := by
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  obtain ⟨a, ha⟩ := ((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).1 h
  obtain ⟨g, -, hg⟩ := exists_step_smul Ch sel mu P hd a _ _ ha
  refine congrArg (Sigma.mk ()) ?_
  rw [← (stepX Ch sel mu P).rp_spec () c, ← (stepX Ch sel mu P).rp_spec () c']
  exact Quotient.sound ⟨g, hg⟩

def clEquiv : (stepX Ch sel mu P).Cl ≃ (mtildeGSD W Ch sel mu P).Cl :=
  Equiv.ofBijective _ ⟨rowCl_injective W Ch sel mu P hd, rowCl_surjective W Ch sel mu P⟩

def rowSec : (mtildeGSD W Ch sel mu P).Sec where
  rep c := rowPt Ch sel mu P ((clEquiv W Ch sel mu P hd).symm c)
  spec c := (clEquiv W Ch sel mu P hd).apply_symm_apply c

theorem clInv_cls {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (C C' : CoefPk X n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (d : DecoSet X.E n ST SG) :
    clInv C C' Λ ((formGSD C' Λ.inv).cls d) = (formGSD C Λ).cls d := rfl

def dualEquiv : (stepX Ch sel mu P).Cl ≃ (dualGSD W Ch sel mu P).Cl := (clEquiv W Ch sel mu P hd).trans (clInv _ _ _)

def dualSec : (dualGSD W Ch sel mu P).Sec where
  rep c := rowPt Ch sel mu P ((dualEquiv W Ch sel mu P hd).symm c)
  spec c := (clInv_cls _ _ _ _).symm.trans ((dualEquiv W Ch sel mu P hd).apply_symm_apply c)

theorem dualSec_rep (c : (stepX Ch sel mu P).Cl) :
    (dualSec W Ch sel mu P hd).rep (dualEquiv W Ch sel mu P hd c) = rowPt Ch sel mu P c :=
  congrArg (rowPt Ch sel mu P) ((dualEquiv W Ch sel mu P hd).symm_apply_apply c)

theorem rowSec_rep (c : (stepX Ch sel mu P).Cl) :
    (rowSec W Ch sel mu P hd).rep (clEquiv W Ch sel mu P hd c) = rowPt Ch sel mu P c :=
  congrArg (rowPt Ch sel mu P) ((clEquiv W Ch sel mu P hd).symm_apply_apply c)

include hd in

theorem card_stab (c : (stepX Ch sel mu P).Cl) : Nat.card ((stepX Ch sel mu P).Stab c) =
    Nat.card (MulAction.stabilizer (mtildeGSD W Ch sel mu P).G (rowPt Ch sel mu P c)) := by
  refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd _)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun g => ?_)
  exact (trivPt X _ _ _ _).symm.injective.eq_iff.symm

include hd in

theorem dual_rho (g : (stepX Ch sel mu P).G ()) :
    (dualGSD W Ch sel mu P).ρ (toRowG Ch sel mu P g) = (stepX Ch sel mu P).rho X.emb W.sgTrue () g := by
  have e : (stepX Ch sel mu P).chr () g = (rowTy Ch sel mu P).chr (toRowG Ch sel mu P g).2 :=
    (chr_stepX Ch sel mu P hd g).trans ((congrArg (·⁻¹) (chr_inv _ _)).trans (inv_inv _))
  exact congrArg (fun a : X.Kˣ => (a : X.K) • rhoVr X.emb W.sgTrue (ufGL _ _ g.1)) e.symm

variable (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok)

def toStep : (dualGSD W Ch sel mu P).EqFun →ₗ[X.K] (stepX Ch sel mu P).FormsK X.emb W.sgTrue hF where
  toFun φ := ⟨fun c => φ.1 (rowPt Ch sel mu P c), fun c γ => by
    have h1 := φ.2 (toRowG Ch sel mu P γ.1) (rowPt Ch sel mu P c)
    have h2 : (toRowG Ch sel mu P γ.1) • rowPt Ch sel mu P c = rowPt Ch sel mu P c :=
      (toRow_smul Ch sel mu P γ.1 _).symm.trans (congrArg (fun q => toRow sel mu q.1.1) γ.2)
    rw [dual_rho W Ch sel mu P hd] at h1
    exact h1.symm.trans (congrArg φ.1 h2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toStep_bijective (h' : (dualGSD W Ch sel mu P).Ok) : Function.Bijective (toStep W Ch sel mu P hd hF) := by
  constructor
  · intro φ ψ h
    apply ((dualGSD W Ch sel mu P).resOf h' (dualSec W Ch sel mu P hd)).injective
    exact Subtype.ext (funext fun c => congrFun (congrArg Subtype.val h) ((dualEquiv W Ch sel mu P hd).symm c))
  · intro x
    let f : ((dualGSD W Ch sel mu P).toCSDOf h' (dualSec W Ch sel mu P hd)).Forms :=
      ⟨fun c => x.1 ((dualEquiv W Ch sel mu P hd).symm c), fun c γ => by
        obtain ⟨g, h1, h2⟩ := exists_step_smul Ch sel mu P hd γ.1 _ _ γ.2
        have h3 := x.2 ((dualEquiv W Ch sel mu P hd).symm c) ⟨g, h2⟩
        refine Eq.trans ?_ h3
        show (dualGSD W Ch sel mu P).ρ γ.1 _ = (stepX Ch sel mu P).rho X.emb W.sgTrue () g _
        rw [← dual_rho W Ch sel mu P hd, h1]
        rfl⟩
    obtain ⟨φ, hφ⟩ := ((dualGSD W Ch sel mu P).resOf h' (dualSec W Ch sel mu P hd)).surjective f
    refine ⟨φ, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c, rfl⟩ := (dualEquiv W Ch sel mu P hd).symm.surjective c
    exact congrFun (congrArg Subtype.val hφ) c

def ofStep (h' : (dualGSD W Ch sel mu P).Ok) :
    (stepX Ch sel mu P).FormsK X.emb W.sgTrue hF ≃ₗ[X.K] (dualGSD W Ch sel mu P).EqFun :=
  (LinearEquiv.ofBijective _ (toStep_bijective W Ch sel mu P hd hF h')).symm

theorem ofStep_val (h' : (dualGSD W Ch sel mu P).Ok) (x : (stepX Ch sel mu P).FormsK X.emb W.sgTrue hF)
    (c : (stepX Ch sel mu P).Cl) : (ofStep W Ch sel mu P hd hF h' x).1 (rowPt Ch sel mu P c) = x.1 c :=
  congrFun (congrArg Subtype.val
    ((LinearEquiv.ofBijective _ (toStep_bijective W Ch sel mu P hd hF h')).apply_symm_apply x)) c

end Step

section Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))
  (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok) (h' : (dualGSD W Ch sel mu P).Ok)

theorem mem_hlat_iff (x : (stepX Ch sel mu P).FormsK X.emb W.sgTrue hF) :
    x ∈ ((stepX Ch sel mu P).hlat X.emb W.sgTrue hF).L ↔
      ofStep W Ch sel mu P hd hF h' x ∈ (dualGSD W Ch sel mu P).intDel := by
  rw [GSD.mem_intDel_iff _ h' (dualSec W Ch sel mu P hd), (dualEquiv W Ch sel mu P hd).surjective.forall]
  refine forall_congr' fun c => ?_
  rw [dualSec_rep, ofStep_val]
  exact Iff.of_eq (congrArg (fun L => x.1 c ∈ delAtr X.emb W.sgTrue L) (Lsh_eq_N (rowPt Ch sel mu P c)))

theorem isFormsOf_hlat (hX : X.Ok) : IsFormsOf _ h' (dualGSD W Ch sel mu P).intDel
    ((stepX Ch sel mu P).hlat X.emb W.sgTrue hF) (ofStep W Ch sel mu P hd hF h') := by
  refine ⟨mem_hlat_iff W Ch sel mu P hd hF h', fun v x => ?_⟩
  have hG : ((dualGSD W Ch sel mu P).gramV.map v.embedding).PosDef := by
    rw [dual_gramV]; exact gramB_posDef _ _
  have hb : ((stepX Ch sel mu P).csd X.emb W.sgTrue hF).HasRatBasis := FormsDescent.hasRatBasis_of_act _ fun c γ i j => by
    have h1 := dual_act_rat W Ch sel mu P hX (toRowG Ch sel mu P γ.1) i j
    rw [dual_rho W Ch sel mu P hd] at h1
    exact h1
  refine (normAt_sq ((stepX Ch sel mu P).csd X.emb W.sgTrue hF) v hb hG x).trans ?_
  letI := h'.fintypeCl
  rw [ipAt_sec v _ h' (dual_act_rat W Ch sel mu P hX) (dualSec W Ch sel mu P hd)]
  letI : Fintype (stepX Ch sel mu P).Cl := ((stepX Ch sel mu P).csd X.emb W.sgTrue hF).finCl
  refine Fintype.sum_equiv (dualEquiv W Ch sel mu P hd) _ _ fun c => ?_
  rw [dualSec_rep, ofStep_val, ← card_stab_inv _ (rowVal W (rowSG Pr sel mu)), ← card_stab W Ch sel mu P hd]
  exact congrArg₂ (fun (k : ℕ) (a : ℂ) => (k : ℂ)⁻¹ * a) (@Nat.card_eq_fintype_card _ (_)).symm
    (pairAt_eq (dualGSD W Ch sel mu P) v (x.1 c)).symm

theorem classSum_ofStep [Fintype (stepX Ch sel mu P).Cl] (h : (mtildeGSD W Ch sel mu P).Ok)
    (x : (stepX Ch sel mu P).FormsK X.emb W.sgTrue hF) (z : (mtildeGSD W Ch sel mu P).EqFun) :
    classSum W Ch sel mu P h (ofStep W Ch sel mu P hd hF h' x) z = ∑ c : (stepX Ch sel mu P).Cl,
      ((Nat.card ((stepX Ch sel mu P).Stab c) : ℕ) : X.K)⁻¹ * pairBK W.sgTrue (x.1 c) (z.1 (rowPt Ch sel mu P c)) := by
  letI := h.fintypeCl
  refine ((rowPair W Ch sel mu P).sumOf_indep h _ (rowSec W Ch sel mu P hd) _ z).trans ?_
  refine (Fintype.sum_equiv (clEquiv W Ch sel mu P hd) _ _ fun c => ?_).symm
  rw [GSD.wt_eq, rowSec_rep, card_stab W Ch sel mu P hd, ← ofStep_val W Ch sel mu P hd hF h' x c]
  rfl

end Lattice

section Pol

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem map_fockB {τ : Type} (f g : MvPolynomial τ K) : σ (fockB f g) = fockB (MvPolynomial.map σ f) (MvPolynomial.map σ g) := by
  rw [fockB_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), fockB, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, map_natCast, MvPolynomial.coeff_map, MvPolynomial.coeff_map]

theorem map_pairB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    σ (pairB lam F F') = pairB lam (MvPolynomial.map σ F) (MvPolynomial.map σ F') := by
  rw [pairB_apply, pairB_apply, map_mul, map_inv₀, map_fockB, extNormB, extNormB, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [map_fockB, Formalism.L2.DIV.map_extremal]

theorem polOf_evV {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) (x : VV K lam) :
    polOf (Gr emb σ n) (Formalism.L2.Forms.shiftOf lam) (fr0 emb σ n) (evV emb 1 lam σ x) = MvPolynomial.map σ x.1 := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun _ => inv_one
  rw [evV_apply, ← e, polOf_fnOf]

end Pol

theorem period_embF {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hI : I.Ok) (hQ : Q.Ok)
    (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (x : Q.S'.FormsK emb Q.sgT hF) (F : Q.Mt emb σ)
    (y : Q.S'.Cl → VV K Q.sgT) (hy : ∀ c, Q.rd emb σ F c = MvPolynomial.map σ (y c).1) :
    (Q.per emb σ hI hQ hc).period (Q.S'.embF emb σ Q.sgT hF x) F = letI := Q.clFin hQ
      σ (∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : K)⁻¹ * pairBK Q.sgT (x.1 c) (y c)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  rw [pairBK_apply, map_pairB, ← hy, ← polOf_evV σ emb]
  rfl

section Layer

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b))

@[reducible] def perOn : PerIn I where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H := H

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

include hd in

theorem row_law (z : (mtildeGSD W Ch sel mu P).EqFun) (g : (stepX Ch sel mu P).G ()) (d : (stepX Ch sel mu P).D ()) :
    MvPolynomial.map σ (z.1 (toRow sel mu (letI := (stepX Ch sel mu P).actD (); g • d : (stepX Ch sel mu P).D ()).1.1)).1 =
      (σ ((stepX Ch sel mu P).chr () g : X.K))⁻¹ • rhoP W.sgTrue (embGL (embAt σ X.emb) ((stepX Ch sel mu P).gam () g))
        (MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1) := by
  have h1 := z.2 (toRowG Ch sel mu P g) (toRow sel mu d.1.1)
  rw [mtilde_rho_toRowG W Ch sel mu P hd] at h1
  have h2 := (congrArg z.1 (toRow_smul Ch sel mu P g d.1.1)).trans h1
  refine (congrArg (fun y : VV X.K W.sgTrue => mapS σ y.1) h2).trans ?_
  refine (LinearMap.map_smulₛₗ (mapS σ) _ (actP W.sgTrue (embGL X.emb (ufGL _ _ g.1)) (z.1 (toRow sel mu d.1.1)).1)).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, mapS_apply, GlobalTheory.ValCmp.use₂]
  congr 1

def rowEmb : (mtildeGSD W Ch sel mu P).EqFun →ₛₗ[σ] (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ where
  toFun z := ⟨fun _ d => MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1, fun _ d =>
    ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ W.sgTrue _ (z.1 (toRow sel mu d.1.1)).2, fun g _ => row_law W Ch sel mu P hd σ z g d⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => map_add (mapS σ) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => LinearMap.map_smulₛₗ (mapS σ) _ _)

variable (hX : X.Ok) (hc : X.Tau → HCParam R)
  {Pl : Rows.Places X.K} (J : AtIn I) (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok)
  (hQ : (perOn W Ch sel mu P b0 til ext tz H).Ok) (l : J.Laws X.emb σ hc)
  (lf : FmLaws J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Pl hI hQ)
  (hT : (perOn W Ch sel mu P b0 til ext tz H).Over J)

section AnyLattice

variable {Λ' : HLat X.K} {ι : Λ'.V ≃ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun}
  (hι : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P) Λ' ι)

include hι

theorem isConcrete_forms : IsConcrete W Ch sel mu P (mtildeOk W Ch sel mu hX P) (dualOk W Ch sel mu P hX) σ
    (forms J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Z hI hJ hQ l lf hT).ptLat Λ' fun x z =>
      ((perOn W Ch sel mu P b0 til ext tz H).per X.emb σ hI hQ hc).period
        ((forms J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Z hI hJ hQ l lf hT).ptEmb x)
        (rowEmb W Ch sel mu P b0 til ext tz H hd σ (ι z)) := by
  refine ⟨ofStep W Ch sel mu P hd lf.famP _, ι, isFormsOf_hlat W Ch sel mu P hd lf.famP _ hX, hι, fun x z => ?_⟩
  letI : Fintype (stepX Ch sel mu P).Cl := (perOn W Ch sel mu P b0 til ext tz H).clFin hQ
  exact (period_embF (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hI hQ hc lf.famP x _
    (fun c => (ι z).1 (rowPt Ch sel mu P c)) fun _ => rfl).trans
    (congrArg σ (classSum_ofStep W Ch sel mu P hd lf.famP _ _ x (ι z)).symm)

end AnyLattice

end Layer

end GlobalTheory.PeriodOnStep
