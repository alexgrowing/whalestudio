import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapStab
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapCls
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SharpRestriction.InertJacobiLevels.TrivialDatumMultiplicitySpaceSubsingleton
import Formalism.LocalRingCardinality.DataMink

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

theorem asm_not_both {p q : ℕ} (h : Nat.Coprime p q) (v : HeightOneSpectrum (𝓞 F)) (hp : (p : 𝓞 F) ∈ v.asIdeal)
    (hq : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  have hg := Nat.gcd_eq_gcd_ab p q
  rw [h] at hg
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    have : (1 : 𝓞 F) = ((p : ℤ) : 𝓞 F) * ((Nat.gcdA p q : ℤ) : 𝓞 F) + ((q : ℤ) : 𝓞 F) * ((Nat.gcdB p q : ℤ) : 𝓞 F) := by
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, ← hg]; simp
    rw [this]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ (by simpa using hp)) (v.asIdeal.mul_mem_right _ (by simpa using hq))
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem asm_exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ v.asIdeal := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ |>.isMaximal (by simpa using hpZ.ne_zero)
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  have hmem : (p : 𝓞 F) ∈ Q := by
    have : (p : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

end SlopeTestRemainingChoices

section Col

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (sp : Spaces R F E)

def parOf (gp : Fin 2 → ℕ) (T : ℕ) (pz : 𝓞 E) (a : Fin 2 → E) : Par F E R.k := ⟨sp.cm.sig, sp.gram0, gp, T, pz, a⟩

def latBack (M : Submodule (𝓞 E) (Fin R.k → E)) : Submodule (𝓞 E) (sp.X 0).V :=
  M.comap ((sp.crd0 : (sp.X 0).V →ₗ[E] (Fin R.k → E)).restrictScalars (𝓞 E))

theorem crdLat0_latBack (M : Submodule (𝓞 E) (Fin R.k → E)) : sp.crdLat0 (latBack sp M) = M :=
  Submodule.map_comap_eq_of_surjective
    (f := (sp.crd0 : (sp.X 0).V →ₗ[E] (Fin R.k → E)).restrictScalars (𝓞 E)) sp.crd0.surjective M

theorem latBack_eq_map (M : Submodule (𝓞 E) (Fin R.k → E)) :
    latBack sp M = M.map ((sp.crd0.symm : (Fin R.k → E) →ₗ[E] (sp.X 0).V).restrictScalars (𝓞 E)) := by
  ext x
  constructor
  · intro hx
    exact ⟨sp.crd0 x, hx, sp.crd0.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    show sp.crd0 (sp.crd0.symm y) ∈ M
    rwa [sp.crd0.apply_symm_apply]

theorem latBack_isLattice (M : Submodule (𝓞 E) (Fin R.k → E)) (h : Submodule.IsLattice E M) :
    Submodule.IsLattice E (latBack sp M) where
  fg := by rw [latBack_eq_map]; exact h.fg.map _
  span_eq_top := by
    rw [latBack_eq_map]
    have : ((M.map ((sp.crd0.symm : (Fin R.k → E) →ₗ[E] (sp.X 0).V).restrictScalars (𝓞 E)) :
        Submodule (𝓞 E) (sp.X 0).V) : Set (sp.X 0).V) =
        (sp.crd0.symm : (Fin R.k → E) →ₗ[E] (sp.X 0).V) '' (M : Set (Fin R.k → E)) := rfl
    rw [this, Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact sp.crd0.symm.surjective

end Col

namespace Par

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ} (P : Par F E k)

theorem T_Ld {d : ℕ} (h : P.LbOK d) : ∀ y ∈ P.Ld, (P.T : E) • y ∈ P.Lb := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h.dual y hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem T_LdV {d : ℕ} (h : P.LbOK d) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ x ∈ P.LdV v, (P.T : intV E v) • x ∈ P.LbV v := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨(P.T : E) • y, P.T_Ld h y hy, ?_⟩
    ext i
    simp [Subring.smul_def]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem fT_L (v : HeightOneSpectrum (𝓞 F)) (x : P.LdV v) (hx : x.1 ∈ P.LbV v) : P.fT v x = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_sup_left hx)

theorem fT_T {d : ℕ} (h : P.LbOK d) (v : HeightOneSpectrum (𝓞 F)) (x : P.LdV v) :
    P.fT v ((P.T : intV E v) • x) = 0 := P.fT_L v _ (P.T_LdV h v x.1 x.2)

theorem pz_fM (v : HeightOneSpectrum (𝓞 F)) (y : P.fM v) : P.pzV v • y = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_sup_right ⟨x, rfl⟩)

theorem fT_ne (v : HeightOneSpectrum (𝓞 F)) (hc : Nat.card (P.fM v) ≠ 1) : P.fT v ≠ 0 := by
  intro h0
  apply hc
  have : Subsingleton (P.fM v) := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (LinearMap.congr_fun h0 x).trans (LinearMap.congr_fun h0 y).symm⟩
  exact Nat.card_unique

theorem UlocAlt (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) (h : (P.T : 𝓞 F) ∈ v.asIdeal) :
    P.Uloc S v = levelVL P.σ P.J v P.Lb ⊓ stabFun _ (P.fT v) := by
  unfold Uloc; rw [if_pos h]

theorem Uloc_hyp (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) (h0 : (P.gp 0 : 𝓞 F) ∉ v.asIdeal)
    (h1 : (P.gp 1 : 𝓞 F) ∉ v.asIdeal) (h : (P.T : 𝓞 F) ∉ v.asIdeal) :
    P.Uloc S v = levelVL P.σ P.J v P.Lb := by
  unfold Uloc; rw [if_neg h, dif_neg h0, dif_neg h1]

theorem Uloc_g (S : P.Splits) (hT : ∀ i, Nat.Coprime P.T (P.gp i)) (hg : Nat.Coprime (P.gp 0) (P.gp 1)) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (P.gp i : 𝓞 F) ∈ v.asIdeal),
      P.Uloc S v = P.iwPre v (S i v h).φ
  | 0, v, h => by
    unfold Uloc; rw [if_neg (fun hh => asm_not_both (hT 0) v hh h), dif_pos h]
  | 1, v, h => by
    unfold Uloc; rw [if_neg (fun hh => asm_not_both (hT 1) v hh h), dif_neg (fun hh => asm_not_both hg v hh h), dif_pos h]

theorem Uloc_lev (S : P.Splits) (hiw : P.IwLe) (v : HeightOneSpectrum (𝓞 F)) :
    P.Uloc S v ≤ levelVL P.σ P.J v P.Lb := by
  unfold Uloc
  split_ifs with h h0 h1
  · exact inf_le_left
  · exact hiw 0 v h0 _
  · exact hiw 1 v h1 _
  · exact le_rfl

theorem U_eq (S : P.Splits) (x : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    x ∈ P.U S ↔ x ∈ UPts P.σ P.J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ P.Uloc S v :=
  Subgroup.mem_inf.trans (and_congr Iff.rfl (Subgroup.mem_iInf.trans (forall_congr' fun _ => Subgroup.mem_comap)))

end Par

section Col

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (sp : Spaces R F E)

def colLevel {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (A : ColumnsAtT R C)
    (clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V) (pz : 𝓞 E) (a : Fin 2 → E)
    (S : (parOf sp gp A.T pz a).Splits)
    (e : C.cls 0 ≃ (parOf sp gp A.T pz a).Cls S)
    (hst : ∀ c, Subsingleton (C.stab 0 c))
    (hl : ∀ c, sp.crdLat0 (clsLat 0 c) =
      CS.globLat ((Quotient.out (e c) : (parOf sp gp A.T pz a).GA) : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
        (parOf sp gp A.T pz a).Lb)
    (hLb : (parOf sp gp A.T pz a).LbOK (2 * R.f)) (hcard : (parOf sp gp A.T pz a).FMCard)
    (hiw : (parOf sp gp A.T pz a).IwLe) (hcp : (parOf sp gp A.T pz a).UCompact)
    (hop : (parOf sp gp A.T pz a).UOpen) (hstab : (parOf sp gp A.T pz a).StabTriv)
    (hTg : ∀ i, Nat.Coprime A.T (gp i)) (hg01 : Nat.Coprime (gp 0) (gp 1)) (hg0 : (gp 0).Prime) :
    ColLevel R F E sp gp C A clsLat where
  Lb := (parOf sp gp A.T pz a).Lb
  Lb_fin := hLb.fin
  Lb_span := hLb.span
  Lb_int := hLb.int
  Lb_dual := hLb.dual
  Lb_index := hLb.index
  Uloc := (parOf sp gp A.T pz a).Uloc S
  Uloc_le := fun v => ((parOf sp gp A.T pz a).Uloc_lev S hiw v).trans inf_le_left
  Uloc_lev := (parOf sp gp A.T pz a).Uloc_lev S hiw
  Uloc_hyp := fun v h0 h1 h => (parOf sp gp A.T pz a).Uloc_hyp S v h0 h1 h
  splitG := fun i v h => (S i v h).φ
  splitG_sig := fun i v h x => (S i v h).sig x
  frG := fun _ _ _ => 1
  Uloc_g := fun i v h x hx => by
    rw [(parOf sp gp A.T pz a).Uloc_g S hTg hg01 i v h, inv_one, one_mul, mul_one]
    exact ⟨fun hh => hh.2, fun hh => ⟨hx, hh⟩⟩
  fM := fun v _ => (parOf sp gp A.T pz a).fM v
  fM_acg := fun _ _ => inferInstance
  fM_mod := fun _ _ => inferInstance
  fT := fun v _ => (parOf sp gp A.T pz a).fT v
  fT_ne := fun v h => (parOf sp gp A.T pz a).fT_ne v (by rw [hcard v h]; exact A.T_prime.ne_one)
  fT_T := fun v _ x => (parOf sp gp A.T pz a).fT_T hLb v x
  fM_card := fun v h => hcard v h
  fT_L := fun v _ x hx => (parOf sp gp A.T pz a).fT_L v x hx
  UlocAlt := fun v h => (parOf sp gp A.T pz a).UlocAlt S v h
  U := (parOf sp gp A.T pz a).U S
  U_eq := (parOf sp gp A.T pz a).U_eq S
  U_compact := hcp S
  U_open := hop S
  w1 := (asm_exists_place (F := F) (gp 0) hg0).choose
  reflection_mem_Glev_castSucc := (asm_exists_place (F := F) (gp 0) hg0).choose_spec
  y := fun c => Quotient.out (e c)
  y_bij := by
    have h : ∀ c : C.cls 0, (Quotient.mk'' (Quotient.out (e c)) : (parOf sp gp A.T pz a).Cls S) = e c :=
      fun c => Quotient.out_eq _
    constructor
    · intro c c' hcc
      exact e.injective ((h c).symm.trans (hcc.trans (h c')))
    · intro z
      exact ⟨e.symm z, (h _).trans (e.apply_symm_apply z)⟩
  y_lat := fun c x => by
    rw [hl c]
    exact Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin R.k) (parOf sp gp A.T pz a).Lb hLb.fin hLb.span _ x
  stabI := fun _ => 1
  stabI_inj := fun c => by
    have := hst c
    exact Function.injective_of_subsingleton _
  stabI_range := fun c γ hγ => by
    constructor
    · rintro ⟨_, hx⟩
      have h1 : γ = 1 := by
        have := congrArg Subtype.val hx
        exact this.symm
      rw [h1, map_one]
      exact one_mem _
    · intro h
      have h1 : γ = 1 := hstab S _ (Quotient.out (e c)).2 γ hγ h
      exact ⟨1, Subtype.ext h1.symm⟩
  stabI_lat := fun c γ x => by simp

end Col

structure Par.AllOK {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
    (P : Par F E k) (d : ℕ) : Prop where
  splits : Nonempty P.Splits
  lb : P.LbOK d
  card : P.FMCard
  iw : P.IwLe
  cp : P.UCompact
  op : P.UOpen
  fin : P.ClsFinite
  stab : P.StabTriv

theorem valW_pos_iff {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (y : K) :
    (0 : WithTop ℤ) < PlacesToy.valW w y ↔ w.valuation K y < 1 := by
  by_cases hy : y = 0
  · subst hy
    rw [PlacesToy.valW_zero, map_zero]
    exact ⟨fun _ => zero_lt_one, fun _ => WithTop.coe_lt_top 0⟩
  · rw [PlacesToy.valW_of_ne w hy]
    have hv : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    unfold vAdd
    rw [Left.neg_pos_iff, ← WithZero.log_one, WithZero.log_lt_log hv one_ne_zero]

def clsPkg (X : Type) [Finite X] (d : ℕ) (hd : 0 < d) : ClsPkg where
  cls := fun i => match i with
    | 0 => X
    | _ + 1 => Empty
  clsFin := fun i => match i with
    | 0 => Fintype.ofFinite X
    | _ + 1 => inferInstanceAs (Fintype Empty)
  stab := fun _ _ => Unit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := d
  DGam_pos := hd
  dvd := fun _ _ => by simp

section HostA

variable {R : Ranks} (H : Host R) (T : ℕ) [hT : Fact T.Prime] (pz : 𝓞 H.E)
  (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))

theorem signature_eq_conjugation : (letI := H.cmStar; (hostSpacesOfNorm H T pz hpz).cm.sig) = conjF H :=
  AlgHom.ext fun x => star_eq_conj H x

theorem gram_matrix_zero_eq_one : (letI := H.cmStar; (hostSpacesOfNorm H T pz hpz).gram0) = 1 := by
  let _ := H.cmStar
  refine Matrix.ext fun i j => ?_
  refine (stdSpace_gram_apply (E := H.E) star_isIntegral (R.N 0) (fun _ => false) (R.N 0) 0 _ _).trans ?_
  simp only [Matrix.one_apply, sgn]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact (if_pos rfl).trans (if_neg Bool.false_ne_true)
  · rw [if_neg h]
    exact if_neg (fun hh => h (Equiv.injective _ hh))

theorem parOf_eq (piG : Fin 2 → 𝓞 H.E) :
    (letI := H.cmStar; parOf (hostSpacesOfNorm H T pz hpz) H.g T pz (fun i => H.conj (piG i : H.E))) = hostPar H T pz piG := by
  let _ := H.cmStar
  simp only [parOf, hostPar, Par.mk.injEq, and_true]
  exact ⟨signature_eq_conjugation H T pz hpz, gram_matrix_zero_eq_one H T pz hpz⟩

end HostA

def parD (D : D7) (u : D.what₂.Word) (pz : 𝓞 D.host.E) (piG : Fin 2 → 𝓞 D.host.E) : Par D.host.F D.host.E D.R.k :=
  letI := D.host.cmStar
  parOf D.sp D.host.g (D.mem u).A.T pz (fun i => D.host.conj (piG i : D.host.E))

theorem levGapD_gen (D : D7) (pz : D.what₂.Word → 𝓞 D.host.E) (piG : Fin 2 → 𝓞 D.host.E)
    (hK : ∀ u, ((pz u : 𝓞 D.host.E) : D.host.E) ∈ D.host.K)
    (hpz : ∀ u, ((pz u : 𝓞 D.host.E) : D.host.E) * D.host.conj (pz u : D.host.E) = ((D.mem u).A.T : D.host.E))
    (hcong : ∀ u, (pz u - 1) ∈
      Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)})
    (hpiK : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K)
    (hpiN : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) * D.host.conj (piG i : D.host.E) = (D.host.g i : D.host.E))
    (ok : ∀ u, (parD D u (pz u) piG).AllOK (2 * D.R.f))
    (S : ∀ u, (parD D u (pz u) piG).Splits)
    (e : ∀ u, (D.mem u).C.cls 0 ≃ (parD D u (pz u) piG).Cls (S u))
    (hst : ∀ u c, Subsingleton ((D.mem u).C.stab 0 c))
    (hl : ∀ u c, (letI := D.host.cmStar; D.sp.crdLat0 (D.clsLat u 0 c)) =
      CS.globLat ((Quotient.out (e u c) : (parD D u (pz u) piG).GA) :
        GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (parD D u (pz u) piG).Lb)
    (hTg : ∀ u i, Nat.Coprime (D.mem u).A.T (D.host.g i))
    (eT : ∀ u, (D.mem u).A.vT ≃ PlT D.host (D.mem u).A.T)
    (tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau))
    (htau : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT)
      (x : 𝓞 D.host.F), x ∈ (eT u v).1.asIdeal ↔
        (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D (tau u w v) (algebraMap D.host.F D.host.E (x : D.host.F)))) :
    Nonempty (LevGapD D) := by
  letI := D.host.cmStar
  exact ⟨{
    lev := fun u => colLevel D.sp (D.mem u).C (D.mem u).A (D.clsLat u) (pz u) (fun i => D.host.conj (piG i : D.host.E))
      (S u) (e u) (hst u) (hl u) (ok u).lb (ok u).card (ok u).iw (ok u).cp (ok u).op (ok u).stab (hTg u)
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne) (D.host.g_prime 0)
    errX :=
      { piG := piG
        piG_K := hpiK
        piG_norm := hpiN
        piT := pz
        piT_K := hK
        piT_norm := hpz
        piT_cong := hcong
        vPl := fun u v => (eT u v).1
        vPl_inj := fun u a b h => (eT u).injective (Subtype.ext h)
        norm_mem_place_ideal := fun u v => (eT u v).2 }
    piG_lev := fun u i v h => (S u i v h).ori
    piT_lev := fun u v z hz y => by
      have hz' : z = (parD D u (pz u) piG).pzV (eT u v).1 := Subtype.ext hz
      rw [hz']
      exact (parD D u (pz u) piG).pz_fM _ y
    tau := tau
    tau_def := htau }⟩

section HostB

variable {R : Ranks} (H : Host R) (T : ℕ) [hT : Fact T.Prime] (pz : 𝓞 H.E)
  (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))

def latOf (a : Fin 2 → H.E) (S : (letI := H.cmStar; parOf (hostSpacesOfNorm H T pz hpz) H.g T pz a).Splits)
    [Finite ((letI := H.cmStar; parOf (hostSpacesOfNorm H T pz hpz) H.g T pz a).Cls S)] (d : ℕ) (hd : 0 < d) :
    letI := H.cmStar
    ∀ i, (clsPkg ((parOf (hostSpacesOfNorm H T pz hpz) H.g T pz a).Cls S) d hd).cls i →
      Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V :=
  letI := H.cmStar
  fun i => match i with
  | 0 => fun c => latBack (hostSpacesOfNorm H T pz hpz)
      (CS.globLat ((Quotient.out c : (parOf (hostSpacesOfNorm H T pz hpz) H.g T pz a).GA) :
        GL (Fin R.k) (H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F)) (parOf (hostSpacesOfNorm H T pz hpz) H.g T pz a).Lb)
  | _ + 1 => fun c => Empty.elim c

end HostB

def LevGapGen (dOf : Ranks → ℕ) : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) [Fact T.Prime] (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}),
    (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) →
    ∃ (K : ClsPkg) (_ : ∀ i, IsEmpty (K.cls (i + 1))) (_ : K.DGam = dOf R)
      (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
      (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c)),
      ∀ hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin hg ht G kb ks tw htw,
        Nonempty (LevGapD (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw))

set_option maxHeartbeats 400000 in
theorem levGapGen_of (dOf : Ranks → ℕ) (hd : ∀ R, 0 < dOf R)
    (h1 : FactSplitG) (h2 : FactLb) (h3 : FactFMCard) (h4 : FactIwLe) (h5 : FactUCompact)
    (h6 : FactUOpen) (h7 : FactClsFinite) (h8 : FactStabTriv) (h9 : FactTNeG) (h10 : FactPlacesT)
    (h11 : FactTau) : LevGapGen dOf := by
  intro R H T hT hlev hpde pz hK hpz hcong hpi
  letI := H.cmStar
  choose piG hpiK hpiN using hpi
  by_cases hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  · have hyp : LevHyp H T pz piG := ⟨hT.out, hK, hpz, hcong, hpiK, hpiN, hg⟩
    have ok : (parOf (hostSpacesOfNorm H T pz hpz) H.g T pz (fun i => H.conj (piG i : H.E))).AllOK (2 * R.f) := by
      rw [parOf_eq]
      exact ⟨⟨fun i v h => Classical.choice (h1 H T pz piG hyp i v h)⟩, h2 H T pz piG hyp, h3 H T pz piG hyp,
        h4 H T pz piG hyp, h5 H T pz piG hyp, h6 H T pz piG hyp, h7 H T pz piG hyp, h8 H T pz piG hyp⟩
    obtain ⟨S⟩ := ok.splits
    haveI := ok.fin S
    obtain ⟨eT⟩ := h10 H T pz piG hyp
    have hTg : ∀ i, Nat.Coprime T (H.g i) := fun i =>
      (Nat.coprime_primes hT.out (H.g_prime i)).2 (h9 H T pz piG hyp i)
    have htau0 : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ e : Fin R.f ≃ ↥(R.Psi), PlacesToy.resCharW w = T →
        ∀ (v : Fin R.f) (x : 𝓞 H.F), x ∈ (eT v).1.asIdeal ↔
          (0 : WithTop ℤ) < PlacesToy.valW w (H.sigmaOf (e v : R.GG) (algebraMap H.F H.E (x : H.F))) := by
      intro w
      by_cases h : PlacesToy.resCharW w = T
      · obtain ⟨e, he⟩ := h11 H T pz piG hyp w (h ▸ PlacesToy.resCharW_mem w)
        exact ⟨eT.trans e, fun _ v x => (he (eT v) x).trans (valW_pos_iff _ _).symm⟩
      · exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_realPlaces_eq_degree]), fun hh => absurd hh h⟩
    choose tauF htau using htau0
    refine ⟨clsPkg ((parOf (hostSpacesOfNorm H T pz hpz) H.g T pz (fun i => H.conj (piG i : H.E))).Cls S) (dOf R) (hd R),
      fun _ => ⟨fun c => Empty.elim c⟩, rfl, latOf H T pz hpz _ S (dOf R) (hd R), ?_, ?_⟩
    · intro i c
      match i, c with
      | 0, c =>
        exact latBack_isLattice _ _ (Formalism.UG.P.global_lattice_isLattice_holds H.F H.E (Fin R.k) _ ok.lb.fin ok.lb.span _)
      | _ + 1, c => exact Empty.elim c
    · intro hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin hg' ht G kb ks tw htw
      refine levGapD_gen _ (fun _ => pz) piG ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => S) (fun _ => Equiv.refl _) ?_ ?_ ?_
        (fun _ => eT) (fun _ w => tauF w) ?_
      · exact fun _ => hK
      · exact fun _ => hpz
      · exact fun _ => hcong
      · exact hpiK
      · exact hpiN
      · exact fun _ => ok
      · exact fun _ _ => inferInstanceAs (Subsingleton Unit)
      · exact fun _ c => crdLat0_latBack _ _
      · exact fun _ => hTg
      · exact fun _ w hw v x => htau w hw v x
  · refine ⟨clsPkg Empty (dOf R) (hd R), fun _ => ⟨fun c => Empty.elim c⟩, rfl,
      fun i => match i with
        | 0 => fun c => Empty.elim c
        | _ + 1 => fun c => Empty.elim c, ?_, ?_⟩
    · intro i c
      match i, c with
      | 0, c => exact Empty.elim c
      | _ + 1, c => exact Empty.elim c
    · intro hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin hg' ht G kb ks tw htw
      exact absurd hg' hg

theorem asm_minkM_pos (n : ℕ) : 0 < minkM n := by
  show 0 < Formalism.HermitianLatticeCounting.S6.minkowskiM n
  unfold Formalism.HermitianLatticeCounting.S6.minkowskiM
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.1 hp).2) _

theorem levGap_of (h1 : FactSplitG) (h2 : FactLb) (h3 : FactFMCard) (h4 : FactIwLe) (h5 : FactUCompact)
    (h6 : FactUOpen) (h7 : FactClsFinite) (h8 : FactStabTriv) (h9 : FactTNeG) (h10 : FactPlacesT)
    (h11 : FactTau) : Formalism.MainNotions.Inhab.LevGap :=
  levGapGen_of (fun R => minkM (2 * R.f * R.N R.m)) (fun _ => asm_minkM_pos _) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem levGapGen (dOf : Ranks → ℕ) (hd : ∀ R, 0 < dOf R) : LevGapGen dOf :=
  levGapGen_of dOf hd factSplitG Formalism.MainNotions.Gaps.LevGap.factLb factFMCard factIwLe Formalism.MainNotions.Gaps.LevGap.factUCompact
    Formalism.MainNotions.Gaps.LevGap.factUOpen factClsFinite factStabTriv Formalism.MainNotions.Gaps.LevGap.factTNeG
    Formalism.MainNotions.Gaps.LevGap.factPlacesT Formalism.MainNotions.Gaps.LevGap.factTau

theorem levGap : Formalism.MainNotions.Inhab.LevGap :=
  levGapGen (fun R => minkM (2 * R.f * R.N R.m)) (fun _ => asm_minkM_pos _)

theorem levGapOne : LevGapGen (fun _ => 1) := levGapGen (fun _ => 1) (fun _ => one_pos)

end Formalism.MainNotions.Gaps.LG

end
