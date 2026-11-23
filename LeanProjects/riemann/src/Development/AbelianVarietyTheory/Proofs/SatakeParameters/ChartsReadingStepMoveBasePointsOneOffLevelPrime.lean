import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelStep

noncomputable section

namespace GlobalTheory.TwU.MoveOff

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.UG.P Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_one_on (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ S, bc (prV (E := E) v) g' = 1) ∧
      ∀ v ∉ S, bc (prV (E := E) v) g' = bc (prV (E := E) v) g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨g, hg, fun v hv => absurd hv (Finset.notMem_empty v), fun _ _ => rfl⟩
  | insert w S hw ih =>
    obtain ⟨g', hg', h1, h2⟩ := ih
    have key : ∀ v, v ≠ w → bc (prV (E := E) v) (afsplitU w 1 g') = bc (prV (E := E) v) g' := fun v hne => by
      apply Units.ext
      rw [afsplit_coe_bc_prV, afsplit_coe_bc_prV, afsplitU_coe, afsplitC_prV_ne w v hne]
    refine ⟨afsplitU w 1 g', afsplitU_mem w σ J 1 g' (one_mem _) hg', fun v hv => ?_, fun v hv => ?_⟩
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · exact afsplit_right1 v 1 g'
      · rw [key v (fun e => hw (e ▸ hv)), h1 v hv]
    · rw [key v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), h2 v (fun h => hv (Finset.mem_insert_of_mem h))]

theorem finite_over {T : ℕ} (hT : T ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((T : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((T : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem exists_basePt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (hT : T ≠ 0) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hkU : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hkV : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) :
    ∃ k' : GlobalTheory.TwU.basePts S, ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal →
      bc (prV (E := E) v) k'.1 = bc (prV (E := E) v) k := by
  have hS := finite_over (F := F) hT
  obtain ⟨g, hg, h1, h2⟩ := exists_one_on σ J hS.toFinset k hkU
  refine ⟨⟨g, (GlobalTheory.TwU.mem_basePts_iff S g).2 ⟨hg, fun v => ?_, fun v hv => h1 v (hS.mem_toFinset.2 hv)⟩⟩,
    fun v hv => h2 v fun h => hv (hS.mem_toFinset.1 h)⟩
  by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v (hS.mem_toFinset.2 hv)]
    exact one_mem _
  · rw [h2 v fun h => hv (hS.mem_toFinset.1 h)]
    exact hkV v hv

theorem stdLat_finite [StarRing E] (n : ℕ) : Module.Finite (𝓞 E) (Formalism.L2.Col.stdLat E n) := by
  have hs : Formalism.L2.Col.stdLat E n = LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin n)) := by
    ext x
    rw [Formalism.L2.Col.mem_stdLat, LinearMap.mem_range]
    constructor
    · intro h
      choose r hr using h
      exact ⟨r, funext hr⟩
    · rintro ⟨r, rfl⟩ i
      exact ⟨r i, rfl⟩
  rw [hs]
  infer_instance

theorem mem_stab_of_local {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) [Module.Finite (𝓞 E) N]
    (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg : g ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N))
    (hh : ∀ v, bc (prV (E := E) v) h = bc (prV (E := E) v) g ∨ bc (prV (E := E) v) h = 1) :
    h ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N) := by
  rw [GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff] at hg ⊢
  intro v
  rcases hh v with e | e <;> rw [e]
  · exact hg v
  · exact one_mem _

theorem carries_move [StarRing E] {n : ℕ} (T : ℕ) (k k' : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (hk' : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k' = bc (prV (E := E) v) k)
    (hone : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k' = 1)
    (hl : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) :
    Formalism.L2.Herm.Carries (k'⁻¹ * k) (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) := by
  haveI := stdLat_finite (E := E) n
  have hs : (k⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := hl
  have key : (k'⁻¹ * k)⁻¹ ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.L2.Col.stdLat E n)) := by
    refine mem_stab_of_local _ _ _ hs fun v => ?_
    by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
    · left
      rw [map_inv, map_inv, map_mul, map_inv, hone v hv, inv_one, one_mul]
    · right
      rw [map_inv, map_mul, map_inv, hk' v hv, inv_mul_cancel, inv_one]
  exact key

theorem adAt_move [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (k k' : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h : bc (prV (E := E) (P.under (𝓞 F))) k' = 1) (r j : Fin n) :
    adAt F P (((k'⁻¹ * k)⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))).1 r j) =
      adAt F P ((k⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))).1 r j) := by
  apply GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV
  have h2 : bc (prV (E := E) (P.under (𝓞 F))) ((k'⁻¹ * k)⁻¹) = bc (prV (E := E) (P.under (𝓞 F))) k⁻¹ := by
    rw [map_inv, map_mul, map_inv, h, inv_one, one_mul, map_inv]
  exact congrArg (fun g : GL (Fin n) (TensorProduct F E ((P.under (𝓞 F)).adicCompletion F)) => g.1 r j) h2

end GlobalTheory.TwU.MoveOff

end

noncomputable section

namespace GlobalTheory.TwU.AtTrue

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem mem_UPts_one {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}
    (hJ : J = 1) {R : Type} [CommRing R] [Algebra F R] {g : GL (Fin n) (TensorProduct F E R)} (h : g ∈ UPts σ J R) : g ∈ UPts σ 1 R := by
  subst hJ
  exact h

theorem std_move {B : Base} {n : ℕ} (T : ℕ) (k k' : GA B n)
    (hk' : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (T : 𝓞 B.host.F) ∉ v.asIdeal →
      bc (prV (E := B.host.E) v) k' = bc (prV (E := B.host.E) v) k)
    (hone : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (T : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) k' = 1)
    (hU : k' ∈ Formalism.L2.Herm.UstdAf B.sp.cm n)
    (h : ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) :
    ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k'⁻¹ * k) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  obtain ⟨p, hp, hN⟩ := h
  refine ⟨p, ⟨mul_mem (inv_mem hU) hp.uni, ?_, fun P => absurd P.2 (Finset.notMem_empty _),
    fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _)⟩, hN⟩
  have hl := hp.lat
  rw [hN] at hl ⊢
  exact GlobalTheory.TwU.MoveOff.carries_move T k k' hk' hone hl

theorem kT_move {B : Base} {X : PreX B.toPre} (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} (k k' : GA B n)
    (hone : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) k' = 1)
    (h : ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    (P : (B.primes X).vT u) (r j : Fin n) (hr : r.1 + 1 = n) :
    HasRes P.1 (adAt B.host.F P.1 (((k'⁻¹ * k)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  have hTP : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
    have h1 := (rls_vT_iff (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u P.1).1 P.2
    have h2 : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal := by
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.1.asIdeal
    rw [map_natCast]
    exact h2
  rw [GlobalTheory.TwU.MoveOff.adAt_move P.1 k k' (hone _ hTP) r j]
  exact h P r j hr

theorem reads_move {B : Base} {X : PreX B.toPre} (I : TC B X) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch} {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))}
    {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (R : I.Reads u a i chOf Lb U chi y st k) (k' : Ch → GA B (B.R.N i))
    (U' : Ch → Subgroup (GA B (B.R.N i))) (chi' : ∀ β, U' β →* ℂˣ)
    (hU : ∀ β x, x ∈ U' β ↔ k' β * x * (k' β)⁻¹ ∈ U β)
    (hchi : ∀ β (x : U' β), chi' β x = chi β ⟨k' β * x.1 * (k' β)⁻¹, (hU β x.1).1 x.2⟩)
    (hstd : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf ((k' β)⁻¹ * k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i))
    (hoff : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal →
      bc (prV (E := B.host.E) v) ((k' β)⁻¹ * k β) = 1)
    (hT : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((((k' β)⁻¹ * k β)⁻¹ : GA B (B.R.N i)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) :
    I.Reads u a i chOf Lb U' chi' (fun c => y c * k' (chOf c)) st (fun β => (k' β)⁻¹ * k β) where
  key := R.key
  onto := R.onto
  lb := R.lb
  k_std := hstd
  k_off := fun β v hv _ _ => hoff β v hv
  k_T := hT
  pt := fun c => by
    have e : y c * k' (chOf c) * ((k' (chOf c))⁻¹ * k (chOf c)) = y c * k (chOf c) := by group
    rw [e]
    exact R.pt c
  lev := fun c x q hq => by
    have e : y c * k' (chOf c) * x * ((k' (chOf c))⁻¹ * k (chOf c)) = y c * (k' (chOf c) * x * (k' (chOf c))⁻¹) * k (chOf c) := by
      group
    rw [e] at hq
    exact (hU (chOf c) x).trans (R.lev c _ q hq)
  chr := fun c x κ hκ hq => by
    have e : y c * k' (chOf c) * x.1 * ((k' (chOf c))⁻¹ * k (chOf c)) =
        y c * (k' (chOf c) * x.1 * (k' (chOf c))⁻¹) * k (chOf c) := by group
    rw [e] at hq
    rw [hchi]
    exact R.chr c _ κ hκ hq
  stab := R.stab

end GlobalTheory.TwU.AtTrue

end

noncomputable section

namespace GlobalTheory.TwU.AtTrue

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem readsMove_holds : ReadsMove := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K hK
  obtain ⟨k, R⟩ := hK
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hB := basePi_of_ok hX hPr u
  have hLb : ∀ β, (K β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := fun β => by
    ext x
    exact (R.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have hT0 : B.T u ≠ 0 := (hPr.T_prime u).ne_zero
  have k3 : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) else 0) :=
    fun β P r j hr => by
    have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
      have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
        hB.conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact @Ne.isUnit (Res P.1) _ _ h0
    have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
        Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
      unfold diaT
      rw [dif_pos hu]
      rfl
    rw [e]
    exact R.k_T β P r j hr
  have hkf := fun β => GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel B.sp.cm (B.R.N i) hB (k β) (diaT (Pr := B.primes X) u) (R.k_std β) (k3 β)
  have hk' : ∀ β, ∃ k' : basePts (K β).lev, ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal →
      bc (prV (E := B.host.E) v) k'.1 = bc (prV (E := B.host.E) v) (k β) := fun β => by
    obtain ⟨hkU, hkV, -, -⟩ := hkf β
    refine GlobalTheory.TwU.MoveOff.exists_basePt (K β).lev hT0 (k β) ?_ fun v _ => ?_
    · rw [hgr]
      exact hkU
    · rw [hLb β, hgr]
      exact hkV v
  choose k' hk' using hk'
  let kk : Ch → GA B (B.R.N i) := fun β => (k' β).1
  have hk'' : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal →
      bc (prV (E := B.host.E) v) (kk β) = bc (prV (E := B.host.E) v) (k β) := hk'
  have hone : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal →
      bc (prV (E := B.host.E) v) (kk β) = 1 :=
    fun β v hv => ((mem_basePts_iff _ _).1 (k' β).2).2.2 v hv
  have hU' : ∀ β, kk β ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) :=
    fun β => by
    have h : kk β ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
        (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := ((mem_basePts_iff _ _).1 (k' β).2).1
    have h2 := mem_UPts_one hgr h
    exact h2
  have hoff : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal →
      bc (prV (E := B.host.E) v) ((kk β)⁻¹ * k β) = 1 := fun β v hv => by
    rw [map_mul, map_inv, hk'' β v hv, inv_mul_cancel]
  have hR := reads_move I R kk
    (fun β => (moveChart (K β) (k' β)).lev.U) (fun β => (moveChart (K β) (k' β)).lev.chi) (fun β x => Iff.rfl) (fun β x => rfl)
    (fun β => std_move (B.T u) (k β) _ (hk'' β) (hone β) (hU' β) (R.k_std β)) hoff
    (fun β => kT_move hPr u (k β) _ (hone β) (R.k_T β))
  exact ⟨k', ⟨_, hR, hoff⟩⟩

end GlobalTheory.TwU.AtTrue

end
