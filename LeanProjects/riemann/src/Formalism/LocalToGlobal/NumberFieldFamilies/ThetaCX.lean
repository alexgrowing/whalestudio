import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaC
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Formalism.LocalToGlobal.JointCharacters.TauEEqEmbTau

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host Formalism.L2.JoinChr Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

variable {D : D7}

def plE (τ : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (tauE D τ)

open Classical in

def embAt (τ : D.what₂.Tau) : (plE τ).Completion →+* ℂ :=
  if (plE τ).embedding = tauE D τ then InfinitePlace.Completion.extensionEmbedding (plE τ)
  else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (plE τ))

theorem embAt_alg (τ : D.what₂.Tau) (k : D.host.E) : embAt τ (algebraMap D.host.E (plE τ).Completion k) = tauE D τ k := by
  unfold embAt
  have e1 : InfinitePlace.Completion.extensionEmbedding (plE τ) (algebraMap D.host.E (plE τ).Completion k) =
      (plE τ).embedding k := by simp
  split_ifs with h
  · rw [e1, h]
  · rcases InfinitePlace.embedding_mk_eq (tauE D τ) with h' | h'
    · exact absurd h' h
    · have e2 : (plE τ).embedding = ComplexEmbedding.conjugate (tauE D τ) := h'
      rw [RingHom.comp_apply, e1, e2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem embAt_cont (τ : D.what₂.Tau) : Continuous (embAt τ) := by
  unfold embAt
  split_ifs
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  · exact Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous

theorem conj_tauE_ne (τ τ' : D.what₂.Tau) : ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, tauE_sqrtMinusD, tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos D
  linarith

theorem plE_bij (D : D7) : Function.Bijective (plE (D := D)) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · exact tauE_inj e
    · exact absurd e (conj_tauE_ne τ τ')
  · intro w
    obtain ⟨τ, h | h⟩ := tauE_or w.embedding
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_embedding]⟩
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem plE_complex (τ : D.what₂.Tau) : (plE τ).IsComplex := by
  rw [plE, InfinitePlace.isComplex_mk_iff]
  exact fun h => conj_tauE_ne τ τ h

structure AdBC (D : D7) where
  Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E
  cont : Continuous Φ
  cont' : Continuous Φ.symm
  inc : ∀ k : D.host.E, Φ (incA D k) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) k

  fin : ∀ x, finPart D x = 1 ↔ (Φ x).2 = 1

  inf : ∀ τ x, embAt τ ((Φ x).1 (plE τ)) = cmpAt D τ x

  idem : ∀ P e, IsPlIdem D e P ↔ Φ e = pairA D.host.E 0 (singleV D.host.E P 1)

  int : ∀ x, finPart D x ∈ intAE D ↔ ∀ P, (Φ x).2 P ∈ P.adicCompletionIntegers D.host.E

  idemF : ∀ v, (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).1 = 0 ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), (P.under (𝓞 D.host.F) = v →
      (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 1) ∧
      (P.under (𝓞 D.host.F) ≠ v → (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 0)

def AdeleBC (D : D7) : Prop := Nonempty (AdBC D)

namespace AdBC

variable (B : AdBC D)

def up : (AE D)ˣ →* Ideles D.host.E := Units.map B.Φ.toMonoidHom

def dn : Ideles D.host.E →* (AE D)ˣ := Units.map B.Φ.symm.toMonoidHom

theorem dn_up (x : (AE D)ˣ) : B.dn (B.up x) = x := Units.ext (by simp [up, dn])

theorem up_dn (x : Ideles D.host.E) : B.up (B.dn x) = x := Units.ext (by simp [up, dn])

theorem up_inc (k : D.host.Eˣ) : B.up (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (by simp [up, B.inc]; rfl)

theorem toUnits_cont : Continuous Circle.toUnits := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun z : Circle => z⁻¹)

def toH : chrA D →* HChar D.host.E where
  toFun χ := ⟨(Circle.toUnits.comp χ.1).comp B.dn,
    (toUnits_cont.comp χ.2.1.1).comp (Continuous.units_map _ B.cont'), fun k => by
      rw [← B.up_inc, MonoidHom.comp_apply, B.dn_up, MonoidHom.comp_apply, χ.2.1.2, map_one]⟩
  map_one' := Subtype.ext (MonoidHom.ext fun _ => map_one Circle.toUnits)
  map_mul' _ _ := Subtype.ext (MonoidHom.ext fun _ => map_mul Circle.toUnits _ _)

theorem toH_up (χ : chrA D) (x : (AE D)ˣ) : (((B.toH χ).1 (B.up x) : ℂˣ) : ℂ) = (χ.1 x : ℂ) := by
  show ((Circle.toUnits (χ.1 (B.dn (B.up x))) : ℂˣ) : ℂ) = _
  rw [B.dn_up]
  rfl

theorem toH_inj : Function.Injective B.toH := by
  intro χ χ' h
  apply Subtype.ext
  ext x
  have := congrArg (fun ψ : HChar D.host.E => ((ψ.1 (B.up x) : ℂˣ) : ℂ)) h
  simpa only [toH_up] using this

theorem toH_unitary (χ : chrA D) : (B.toH χ).IsUnitary := by
  intro x
  show ‖((Circle.toUnits (χ.1 (B.dn x)) : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem up_inf (τ : D.what₂.Tau) (u : (plE τ).Completionˣ) (x : (AE D)ˣ) (h1 : finPart D (x : AE D) = 1)
    (h2 : ∀ τ', τ' ≠ τ → cmpAt D τ' (x : AE D) = 1) (h3 : cmpAt D τ (x : AE D) = embAt τ u) :
    B.up x = infIdele D.host.E (plE τ) u := by
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) ((B.fin x).1 h1)
  obtain ⟨τ', rfl⟩ := (plE_bij D).2 w
  apply (embAt τ').injective
  refine (B.inf τ' x).trans ?_
  by_cases e : τ' = τ
  · subst e
    rw [h3]
    exact congrArg _ (infIdele_fst_self D.host.E _ u).symm
  · rw [h2 τ' e, ← (embAt τ').map_one]
    exact congrArg _ (infIdele_fst_ne D.host.E _ _ (fun a => e ((plE_bij D).1 a)) u).symm

theorem toH_inf (χ : chrA D) (a : D.what₂.Tau → ℚ) (h : ∀ τ, HasInfExp D χ.1 τ (a τ)) : (B.toH χ).HasInfQ (embTau D) a := by
  classical
  choose n hn he using h
  refine ⟨n, hn, fun k => ?_⟩
  have e1 : (B.toH χ).inf k = ∏ w : InfinitePlace D.host.E, (B.toH χ).1 (infIdele D.host.E w (atInf w k)) := by
    show (B.toH χ).1 (infDiag k) = _
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [e1, Units.coe_prod, ← Fintype.prod_bijective _ (plE_bij D) _ _ (fun _ => rfl)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hk : tauE D τ k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  let x := mkU (D := D) (fun τ' => if τ' = τ then tauE D τ k else 1) (fun τ' => by split_ifs; exacts [hk, one_ne_zero])
  have h1 : finPart D (x : AE D) = 1 := finPart_mkAE _ _
  have h2 : ∀ τ', τ' ≠ τ → cmpAt D τ' (x : AE D) = 1 := fun τ' h => (cmpAt_mkAE _ _ τ').trans (if_neg h)
  have h3 : cmpAt D τ (x : AE D) = tauE D τ k := (cmpAt_mkAE _ _ τ).trans (if_pos rfl)
  rw [← B.up_inf τ _ x h1 h2 (h3.trans (embAt_alg τ k).symm), B.toH_up, allSome_fam.1 (he τ) x h1 h2]
  have h3' : th0 D τ (infPart D (x : AE D)) = tauE D τ k := h3
  rw [h3']
  rfl

end AdBC

section Dens

variable {L : Type} [Field L] [NumberField L]

def inl1 : ((w : InfinitePlace L) → w.Completion) →* AdeleRing (𝓞 L) L where
  toFun y := ((y : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (mul_one 1).symm

theorem infinite_inclusion_continuous : Continuous (inl1 (L := L)) := continuous_id.prodMk continuous_const

theorem infinite_inclusion_single (w : InfinitePlace L) (u : w.Completionˣ) :
    Units.map inl1 (Units.map (by classical exact MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w) u) =
      infIdele L w u := rfl

theorem infinite_inclusion_diagonal (k : Lˣ) :
    Units.map inl1 (Units.map (algebraMap L ((w : InfinitePlace L) → w.Completion)).toMonoidHom k) = infDiag k := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply]
  simp only [MonoidHom.comp_apply, ← infinite_inclusion_single, ← map_prod]
  congr 1
  apply Units.ext
  rw [Units.coe_prod]
  exact (Finset.univ_prod_mulSingle _).symm

theorem dense_units : DenseRange (Units.map (algebraMap L ((w : InfinitePlace L) → w.Completion)).toMonoidHom) := by
  have h : Dense (Set.range (algebraMap L ((w : InfinitePlace L) → w.Completion))) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap L
  have : Nontrivial ((w : InfinitePlace L) → w.Completion) := inferInstanceAs (Nontrivial (InfiniteAdeleRing L))
  refine (h.preimage Units.isOpenEmbedding_val.isOpenMap).mono ?_
  rintro u ⟨k, hk⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact u.ne_zero hk.symm
  exact ⟨Units.mk0 k h0, Units.ext hk⟩

theorem fin_inf (hc : ∀ w : InfinitePlace L, w.IsComplex) (χ : HChar L) (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) (k : Lˣ) :
    χ.inf k = 1 := by
  obtain ⟨n, hn, hχ⟩ := h
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hc w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz' : e.symm z ^ n = (atInf w k : w.Completion) := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun a => (atInf w k).ne_zero (by rw [← hz', a, zero_pow hn.ne'])
  have e2 : atInf w k = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [MonoidHom.comp_apply, e2, map_pow, map_pow]
  exact DFunLike.congr_fun (congrArg Subtype.val hχ) _

end Dens

namespace AdBC

variable (B : AdBC D)

def secOfH0 (χ : HChar D.host.E) (hu : χ.IsUnitary) : (AE D)ˣ →* Circle where
  toFun x := ⟨χ.1 (B.up x), mem_sphere_zero_iff_norm.2 (hu _)⟩
  map_one' := Circle.ext (by show ((χ.1 (B.up 1) : ℂˣ) : ℂ) = 1; rw [map_one, map_one]; rfl)
  map_mul' x y := Circle.ext (by
    show ((χ.1 (B.up (x * y)) : ℂˣ) : ℂ) = (χ.1 (B.up x) : ℂ) * (χ.1 (B.up y) : ℂ)
    rw [map_mul, map_mul, Units.val_mul])

theorem unitary_hecke_infinity_type (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) (τ : D.what₂.Tau) :
    HasInfExp D (B.secOfH0 χ hu) τ (a τ) := by
  classical
  obtain ⟨n, hn, he⟩ := h
  refine ⟨n τ, hn τ, allSome_fam.2 fun x h1 h2 => ?_⟩
  have hne : ∀ (y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ) τ', embAt τ' (y.1 (plE τ')) ≠ 0 := fun y τ' =>
    ((y.isUnit.map (Pi.evalRingHom (fun w : InfinitePlace D.host.E => w.Completion) (plE τ'))).map (embAt τ')).ne_zero
  have hc : ∀ τ', Continuous fun y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ => embAt τ' (y.1 (plE τ')) :=
    fun τ' => (embAt_cont τ').comp ((continuous_apply _).comp Units.continuous_val)
  have key : ∀ y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ, ((χ.1 (Units.map inl1 y) : ℂˣ) : ℂ) =
      ∏ τ', (embAt τ' (y.1 (plE τ')) / ((‖embAt τ' (y.1 (plE τ'))‖ : ℝ) : ℂ)) ^ n τ' := by
    intro y
    refine dense_units.induction_on y (isClosed_eq ?_ ?_) fun k => ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ infinite_inclusion_continuous))
    · refine continuous_finsetProd _ fun τ' _ => Continuous.zpow₀ ((hc τ').div
        (Complex.continuous_ofReal.comp (hc τ').norm) fun y => ?_) _ fun y => Or.inl ?_
      · exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne y τ'))
      · exact div_ne_zero (hne y τ') (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne y τ')))
    · rw [infinite_inclusion_diagonal]
      refine (he k).trans (Finset.prod_congr rfl fun τ' _ => ?_)
      have : embAt τ' ((Units.map (algebraMap D.host.E ((w : InfinitePlace D.host.E) → w.Completion)).toMonoidHom k).1
        (plE τ')) = embTau D τ' k := embAt_alg τ' k
      rw [this]
  let y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ :=
    Units.map (RingHom.fst (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom (B.up x)
  have ey : Units.map inl1 y = B.up x := Units.ext (Prod.ext rfl ((B.fin x).1 h1).symm)
  have ec : ∀ τ', embAt τ' (y.1 (plE τ')) = th0 D τ' (infPart D (x : AE D)) := fun τ' => B.inf τ' x
  show ((χ.1 (B.up x) : ℂˣ) : ℂ) = _
  rw [← ey, key, Finset.prod_eq_single τ, ec]
  · intro τ' _ h
    rw [ec, h2 τ' h]
    simp
  · intro h
    exact absurd (Finset.mem_univ τ) h

def ofH (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) : chrA D :=
  ⟨B.secOfH0 χ hu, ⟨Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ B.cont))) _,
    fun k => Circle.ext (by
      show ((χ.1 (B.up _) : ℂˣ) : ℂ) = 1
      rw [B.up_inc, χ.2.2]; rfl)⟩, fun τ => ⟨_, B.unitary_hecke_infinity_type χ hu a h τ⟩⟩

theorem toH_ofH (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) :
    B.toH (B.ofH χ hu a h) = χ := by
  apply Subtype.ext
  ext x
  show ((χ.1 (B.up (B.dn x)) : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ)
  rw [B.up_dn]

def ResTriv : Prop := ∀ χ : HChar D.host.E, χ.TrivOn D.host.F → ∀ a, χ.1 (B.up (idF D a)) = 1

def EtaIs : Prop := ∀ χ : chrA D, (B.toH χ).ResEta D.host.F → IsEta D (χ.1.comp (idF D))

def UnrAll : Prop := ∀ χ : chrA D, (∀ v, (B.toH χ).UnrAt v) → UnramEverywhere D χ.1

end AdBC

def EtaU (D : D7) : Prop := ∀ η η', IsEta D η → IsEta D η' → η = η'

structure ChrGaps (B : AdBC D) : Prop where
  triv : B.ResTriv
  etaIs : B.EtaIs
  unr : B.UnrAll
  etaU : EtaU D

theorem hasInf_tau (χ : HChar D.host.E) (n : D.R.Psi → ℤ) (h : χ.HasInf (embPsi D.host) n) :
    χ.HasInf (embTau D) (fun τ => n (D.eTau τ)) := by
  intro k
  rw [h k]
  exact (Fintype.prod_equiv D.eTau
    (fun τ => (embPsi D.host (D.eTau τ) (k : D.host.E) / ((‖embPsi D.host (D.eTau τ) (k : D.host.E)‖ : ℝ) : ℂ)) ^ n (D.eTau τ))
    (fun g => (embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g) (fun _ => rfl)).symm

theorem eta_inf (C : CharFrame D) : C.eta.HasInfQ (embTau D) (fun _ => 1 / 2) :=
  ⟨fun _ => 1, fun _ => by norm_num, hasInf_tau C.eta _ C.isEta.inf⟩

section Frame

variable {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

theorem tup_unitary (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).IsUnitary := by
  obtain ⟨n, hn, h⟩ := Tp.xi_fin μ
  exact (C.isMu0 j).unitary.mul (HChar.isUnitary_of_order hn h)

theorem tup_inf (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).HasInfQ (embTau D) (fun τ => -(D.hc τ).e j) := by
  obtain ⟨n, hn, hinf⟩ := (C.isMu0 j).inf
  refine ⟨fun τ => n (D.eTau τ), fun τ => by rw [hn]; simp [eExp], fun k => ?_⟩
  have h0 := fin_inf (fun w => by obtain ⟨τ, rfl⟩ := (plE_bij D).2 w; exact plE_complex τ) (Tp.xi μ) (Tp.xi_fin μ) k
  show (((C.mu0 j).inf k * (Tp.xi μ).inf k : ℂˣ) : ℂ) = _
  rw [h0, mul_one]
  exact hasInf_tau _ n hinf k

variable (B : AdBC D)

def chrTup (μ : D.what₂.Tup) (j : ℕ) : chrA D :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then B.ofH _ (tup_unitary Tp μ ⟨j - 1, by omega⟩) _ (tup_inf Tp μ _) else 1

theorem chrTup_succ (μ : D.what₂.Tup) (j : Fin D.R.m) :
    chrTup Tp B μ (j.1 + 1) = B.ofH _ (tup_unitary Tp μ j) _ (tup_inf Tp μ j) := by
  have h : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ D.R.m := ⟨by omega, j.2⟩
  simp [chrTup, h]

def chrInOf (G : ChrGaps B) : ChrIn D :=
  have he : IsEta D ((B.ofH C.eta C.isEta.unitary _ (eta_inf C)).1.comp (idF D)) :=
    G.etaIs _ (by rw [B.toH_ofH]; exact C.isEta.res)
  { chr := chrTup Tp B
    chr_exp := fun μ j τ => by rw [chrTup_succ]; exact B.unitary_hecke_infinity_type _ (tup_unitary Tp μ j) _ (tup_inf Tp μ j) τ
    chr_res := fun μ j h1 h2 => by
      unfold chrTup
      rw [dif_pos ⟨h1, h2⟩]
      refine ⟨⟨_, he⟩, fun η _ a => Circle.ext ?_⟩
      rw [pow_zero]
      exact congrArg Units.val (G.triv _ ((C.isMu0 _).triv.mul (Tp.xi_triv μ)) a)
    eta := B.ofH C.eta C.isEta.unitary _ (eta_inf C)
    eta_exp := B.unitary_hecke_infinity_type _ C.isEta.unitary _ (eta_inf C)
    eta_res := ⟨⟨_, he⟩, fun η hη a => by rw [pow_one, G.etaU η _ hη he]; rfl⟩
    eta_unr := G.unr _ (by rw [B.toH_ofH]; exact C.isEta.unr) }

variable {ψ : AddChar (AF D.host.F) ℂ} (Gc : ChrGaps B) (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ)
  (f : Free Om)

def thetaChrOf : ThetaChrTied D C nch Tp (thetaOf D G P hE Om (chrInOf Tp B Gc) f) where
  eChr := B.toH
  inj := B.toH_inj
  range := fun χ => ⟨fun ⟨c, hc⟩ => hc ▸ ⟨B.toH_unitary c, _, B.toH_inf c _ (infTyC_spec c)⟩,
    fun ⟨hu, a, ha⟩ => ⟨B.ofH χ hu a ha, B.toH_ofH χ hu a ha⟩⟩
  infTy := fun c => B.toH_inf c _ (infTyC_spec c)
  chrOf := fun μ j => by
    show B.toH (chrTup Tp B μ (j.1 + 1)) = _
    rw [chrTup_succ, B.toH_ofH]
  etaT := B.toH_ofH _ C.isEta.unitary _ (eta_inf C)

theorem sameChrOf (hS : SpSig D) (hW : WittLow D) :
    SameChr (thetaCompatibilityOf G P hE Om (chrInOf Tp B Gc) f hS hW) (thetaChrOf Tp B Gc G P hE Om f) where
  idem := fun Q => ⟨B.Φ.symm (pairA D.host.E 0 (singleV D.host.E Q 1)), (B.idem Q _).2 (B.Φ.apply_symm_apply _)⟩
  fin := fun c Q e he k x hx => by
    classical
    have e1 : B.up x = localIdele D.host.E Q (atFin Q k) := by
      apply Units.ext
      show B.Φ (x : AE D) = _
      rw [hx, locE, RingEquiv.map_add, RingEquiv.map_mul, RingEquiv.map_sub, RingEquiv.map_one, B.inc, (B.idem Q e).1 he]
      refine Prod.ext ?_ ?_
      · show (1 : InfiniteAdeleRing D.host.E) + 0 * _ = 1
        rw [zero_mul, add_zero]
      · refine RestrictedProduct.ext _ _ fun v => ?_
        show (1 : v.adicCompletion D.host.E) + (Pi.single Q (1 : Q.adicCompletion D.host.E) : ∀ w : HeightOneSpectrum (𝓞 D.host.E),
            w.adicCompletion D.host.E) v * (algebraMap D.host.E (v.adicCompletion D.host.E) k - 1) =
          (Pi.mulSingle Q (algebraMap D.host.E (Q.adicCompletion D.host.E) k) : ∀ w : HeightOneSpectrum (𝓞 D.host.E),
            w.adicCompletion D.host.E) v
        by_cases h : v = Q
        · subst h
          rw [Pi.single_eq_same, Pi.mulSingle_eq_same, one_mul, add_sub_cancel]
        · rw [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h, zero_mul, add_zero]
    refine (B.toH_up c x).symm.trans ?_
    rw [e1]
    rfl
  inf := fun θ hθ c τ k x hx => by
    rw [plOf_eq hθ τ]
    obtain rfl := fam_eq hθ
    have e1 := B.up_inf τ (atInf (plE τ) k) x hx.1 hx.2.1 (hx.2.2.trans ((cmpAt_incA τ k).trans (embAt_alg τ k).symm))
    refine (B.toH_up c x).symm.trans ?_
    rw [e1]
    rfl

end Frame

end Formalism.L2.Fam.ThC

end
