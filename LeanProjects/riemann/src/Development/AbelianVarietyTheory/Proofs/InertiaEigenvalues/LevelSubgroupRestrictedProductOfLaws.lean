import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.IdemSupport GlobalTheory.LevSplit

namespace GlobalTheory.LevelProduct

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem piece_one {e : A} (he : e * e = e) : piece he (1 : GL n A) = 1 :=
  Units.ext (mix_self e _)

theorem piece_mul' {e : A} (he : e * e = e) (x y : GL n A) : piece he (x * y) = piece he x * piece he y :=
  Units.ext (by
    show e • (x.1 * y.1) + (1 - e) • (1 : Matrix n n A) = (e • x.1 + (1 - e) • 1) * (e • y.1 + (1 - e) • 1)
    rw [mix_mul he, Matrix.one_mul])

theorem piece_inv' {e : A} (he : e * e = e) (x : GL n A) : (piece he x)⁻¹ = piece he x⁻¹ := rfl

theorem piece_conj {e : A} (he : e * e = e) (b x : GL n A) :
    b * piece he x * b⁻¹ = piece he (b * x * b⁻¹) := by
  apply Units.ext
  show b.1 * (e • x.1 + (1 - e) • (1 : Matrix n n A)) * (b⁻¹).1 =
    e • (b.1 * x.1 * (b⁻¹).1) + (1 - e) • (1 : Matrix n n A)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]

theorem piece_conj' {e : A} (he : e * e = e) (b x : GL n A) :
    b⁻¹ * piece he x * b = piece he (b⁻¹ * x * b) := by
  simpa using piece_conj he b⁻¹ x

theorem smul_piece_sub {e : A} (he : e * e = e) (x : GL n A) :
    e • ((piece he x).1 - 1) = (piece he x).1 - 1 := by
  have h : (piece he x).1 - 1 = e • (x.1 - 1) := by
    show e • x.1 + (1 - e) • (1 : Matrix n n A) - 1 = _
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h, smul_smul, he]

theorem piece_apply {e : A} (he : e * e = e) (x : GL n A) (i j : n) :
    (piece he x).1 i j = e * x.1 i j + (1 - e) * (1 : Matrix n n A) i j := rfl

theorem mul_one_sub_mul {e : A} (he : e * e = e) (x : A) : e * ((1 - e) * x) = 0 := by
  linear_combination (-x) * he

theorem triv_gen {e : A} (he : e * e = e) (M M' : Matrix n n A) (h : M * M' = 1) (a b : n) :
    e * (M * (e • M' + (1 - e) • (1 : Matrix n n A)) - 1) a b = 0 := by
  have e1 : M * (e • M' + (1 - e) • (1 : Matrix n n A)) - 1 = (1 - e) • (M - 1) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, h, Matrix.mul_one, sub_smul, sub_smul, one_smul, one_smul, smul_sub]
    abel
  rw [e1]
  exact mul_one_sub_mul he _

theorem map_mix {B : Type} [CommRing B] (ψ : A →+* B) (e m d : A) :
    ψ (e * m + (1 - e) * d) = ψ e * ψ m + (1 - ψ e) * ψ d := by
  simp only [map_add, map_mul, map_sub, map_one]

theorem map_one_apply {B : Type} [CommRing B] (ψ : A →+* B) (i j : n) :
    ψ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Generic

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_of_mem_St {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ St β) (i j : Fin n) :
    (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨y, rfl⟩ := hx
  have : β⁻¹ * frGL β y * β = intGL F E n y := by
    show β⁻¹ * (β * intGL F E n y * β⁻¹) * β = _
    group
  rw [this]
  exact (y.1 i j).2

theorem mem_St_of_int {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (a1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (a2 : ∀ i j, (β⁻¹ * x⁻¹ * β).1 i j ∈ Formalism.L2.Herm.intAf F E) : x ∈ St β := by
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, a2 i j⟩
  have hM : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M = (β⁻¹ * x * β).1 := rfl
  have hM' : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M' = (β⁻¹ * x⁻¹ * β).1 := rfl
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p1 : M * M' = 1 := inj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]; simp [mul_assoc])
  have p2 : M' * M = 1 := inj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]; simp [mul_assoc])
  refine ⟨⟨M, M', p1, p2⟩, ?_⟩
  have : intGL F E n ⟨M, M', p1, p2⟩ = β⁻¹ * x * β := Units.ext hM
  show β * intGL F E n ⟨M, M', p1, p2⟩ * β⁻¹ = x
  rw [this]; group

theorem piece_frGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    piece he (frGL β y) = frGL β (piece hφ y) := by
  have h1 : intGL F E n (piece hφ y) = piece he (intGL F E n y) := by
    apply Units.ext
    ext i j
    show (((piece hφ y).1 i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (φ : E ⊗[F] Formalism.L2.Herm.Af F) * ((y.1 i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) +
        (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) * (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j
    rw [piece_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show piece he (β * intGL F E n y * β⁻¹) = β * intGL F E n (piece hφ y) * β⁻¹
  rw [h1, piece_conj]

theorem piece_mem_St {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : x ∈ St β) : piece he x ∈ St β := by
  obtain ⟨y, rfl⟩ := hx
  rw [piece_frGL β hφ he]
  exact ⟨_, rfl⟩

theorem redFn_piece {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : x ∈ St β) (PP : Pl E) (h : resS F PP φ = 1) :
    redFn β PP (piece he x) = redFn β PP x := by
  obtain ⟨y, rfl⟩ := hx
  rw [piece_frGL β hφ he, redFn_frGL, redFn_frGL]
  apply Units.ext
  ext i j
  show resS F PP ((piece hφ y).1 i j) = resS F PP (y.1 i j)
  rw [piece_apply, map_add, map_mul, map_mul, h, map_sub, h, map_one, sub_self, zero_mul, add_zero, one_mul]

theorem redFn_piece_eq_one {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E}
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : piece he x ∈ St β) (PP : Pl E) (h : resS F PP φ = 0) :
    redFn β PP (piece he x) = 1 :=
  redFn_eq_one β PP _ hx φ h (smul_piece_sub he x)

end Stab

section Adelic

variable {D : D7}

def phi (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.L2.Herm.intAf D.host.F D.host.E :=
  adS D.host.F D.host.E (idemAd fun w => w = v)

theorem phi_idem (v : HeightOneSpectrum (𝓞 D.host.F)) : phi D v * phi D v = phi D v := by
  unfold phi
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases h : w = v
  · have e := idemAd_pos (F := D.host.F) (P := fun w => w = v) (v := w) h
    exact (congrArg₂ (· * ·) e e).trans ((one_mul _).trans e.symm)
  · have e := idemAd_neg (F := D.host.F) (P := fun w => w = v) (v := w) h
    exact (congrArg₂ (· * ·) e e).trans ((zero_mul _).trans e.symm)

theorem phi_idem' (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (phi D v : Formalism.IndefR.Lev.EAf D) * (phi D v : Formalism.IndefR.Lev.EAf D) = (phi D v : Formalism.IndefR.Lev.EAf D) :=
  congrArg Subtype.val (phi_idem v)

theorem resS_phi_pos {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : PP.under (𝓞 D.host.F) = v) :
    resS D.host.F PP (phi D v) = 1 :=
  resS_idemAd_pos PP (PP.under (𝓞 D.host.F)) rfl h

theorem resS_phi_neg {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ PP.under (𝓞 D.host.F) = v) :
    resS D.host.F PP (phi D v) = 0 :=
  resS_idemAd_neg PP (PP.under (𝓞 D.host.F)) rfl h

def epsF (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AF D.host.F := (exists_placeIdem (D := D) v).choose

theorem epsF_spec (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (epsF D v) :=
  (exists_placeIdem (D := D) v).choose_spec

def fE (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D := algebraMap _ _ (epsF D v)

theorem fE_idem (v : HeightOneSpectrum (𝓞 D.host.F)) : fE D v * fE D v = fE D v := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  exact place_idem hΦ (epsF_spec v)

theorem fE_conj (v : HeightOneSpectrum (𝓞 D.host.F)) : cA D (fE D v) = fE D v := cA_algebraMap _

theorem fE_inf (v : HeightOneSpectrum (𝓞 D.host.F)) : infPart D (fE D v) = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  exact (place_comp hΦ (epsF_spec v)).1

theorem finSw_fE (v : HeightOneSpectrum (𝓞 D.host.F)) : finSw D (fE D v) = (phi D v : Formalism.IndefR.Lev.EAf D) := by
  obtain ⟨α, h, h1, h0⟩ := epsF_spec (D := D) v
  have hα : α = ((idemAd (F := D.host.F) fun w => w = v : _) : _) := FiniteAdeleRing.ext _ fun w => by
    by_cases hw : w = v
    · subst hw
      exact h1.trans (idemAd_pos (F := D.host.F) (P := fun w' => w' = w) (v := w) rfl).symm
    · exact (h0 w hw).trans (idemAd_neg (F := D.host.F) (P := fun w' => w' = v) (v := w) hw).symm
  unfold fE
  rw [h, hα]
  rfl

def cmp (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* GA D V where
  toFun g := ⟨piece (fE_idem v) g.1, piece_mem _ _ (fE_idem v) (fE_conj v) g.2⟩
  map_one' := Subtype.ext (piece_one (fE_idem v))
  map_mul' x y := Subtype.ext (piece_mul' (fE_idem v) x.1 y.1)

variable (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V)

theorem mt_cmp : mt V (cmp V v g) = fE D v • mt V g + (1 - fE D v) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

theorem cmp_supp : SuppF V (fE D v) (cmp V v g) :=
  (suppF_iff V _ _).2 (smul_mix (fE_idem v) (mt_cmp V v g))

theorem cmp_mem_GfC : cmp V v g ∈ GfC V := mem_GfC_of_suppF V (fE_inf v) (cmp_supp V v g)

theorem cmp_triv : TrivAt V (fE D v) (g * (cmp V v g)⁻¹) := by
  intro a b
  have e1 : mt V g * mt V g⁻¹ = 1 := by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one]
  have e : mt V (g * (cmp V v g)⁻¹) =
      mt V g * (fE D v • mt V g⁻¹ + (1 - fE D v) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) := by
    rw [← map_inv, GlobalTheory.IdemSupport.mt_mul, mt_cmp]
  rw [e]
  exact triv_gen (fE_idem v) _ _ e1 a b

theorem finE_cmp : finE V (cmp V v g) = piece (phi_idem' v) (finE V g) := by
  apply Units.ext
  ext i j
  refine (map_mix (finSw D) (fE D v) (mt V g i j) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)).trans ?_
  rw [finSw_fE, map_one_apply]
  rfl

end Adelic

section Local

variable {D : D7} {ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem one_int {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

def badPl (ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (a : Formalism.IndefR.Lev.EAf D) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.under (𝓞 D.host.F)) ''
    {Q | ι a Q ∉ Q.adicCompletionIntegers D.host.E}

theorem badPl_finite (a : Formalism.IndefR.Lev.EAf D) : (badPl ι a).Finite :=
  (Filter.eventually_cofinite.1 (ι a).2).image _

variable (hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a)
include hι

theorem ι_phi (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ι (phi D v : Formalism.IndefR.Lev.EAf D) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E ((idemAd (F := D.host.F) fun w => w = v : _) : _) := by
  show ι ((1 : D.host.E) ⊗ₜ[D.host.F] _) = _
  rw [hι, map_one, one_mul]
  rfl

theorem ι_phi_pos {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) : ι (phi D v : Formalism.IndefR.Lev.EAf D) Q = 1 := by
  rw [ι_phi hι, GlobalTheory.AdeleBaseChange.adMap_apply]
  exact (congrArg _ (idemAd_pos (F := D.host.F) (P := fun w => w = v) (v := Q.under (𝓞 D.host.F)) h)).trans (map_one _)

theorem ι_phi_neg {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ¬ Q.under (𝓞 D.host.F) = v) : ι (phi D v : Formalism.IndefR.Lev.EAf D) Q = 0 := by
  rw [ι_phi hι, GlobalTheory.AdeleBaseChange.adMap_apply]
  exact (congrArg _ (idemAd_neg (F := D.host.F) (P := fun w => w = v) (v := Q.under (𝓞 D.host.F)) h)).trans (map_zero _)

theorem ι_mix (Q : HeightOneSpectrum (𝓞 D.host.E)) (e a c : Formalism.IndefR.Lev.EAf D) :
    ι (e * a + (1 - e) * c) Q = ι e Q * ι a Q + (1 - ι e Q) * ι c Q := by
  rw [map_mix ι]
  rfl

theorem ι_mix_pos {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) (a c : Formalism.IndefR.Lev.EAf D) :
    ι ((phi D v : Formalism.IndefR.Lev.EAf D) * a + (1 - (phi D v : Formalism.IndefR.Lev.EAf D)) * c) Q = ι a Q := by
  rw [ι_mix hι, ι_phi_pos hι h, one_mul, sub_self, zero_mul, add_zero]

theorem ι_mix_neg {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ¬ Q.under (𝓞 D.host.F) = v) (a c : Formalism.IndefR.Lev.EAf D) :
    ι ((phi D v : Formalism.IndefR.Lev.EAf D) * a + (1 - (phi D v : Formalism.IndefR.Lev.EAf D)) * c) Q = ι c Q := by
  rw [ι_mix hι, ι_phi_neg hι h, zero_mul, sub_zero, one_mul, zero_add]

theorem int_iff (a : Formalism.IndefR.Lev.EAf D) : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι a Q ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun h Q => GlobalTheory.AdeleBaseChange.map_mem_int hι h Q, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩

theorem int_of_local (a c : Formalism.IndefR.Lev.EAf D)
    (h : ∀ v, (phi D v : Formalism.IndefR.Lev.EAf D) * a + (1 - (phi D v : Formalism.IndefR.Lev.EAf D)) * c ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E) : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (int_iff hι a).2 fun Q => by
    have := (int_iff hι _).1 (h (Q.under (𝓞 D.host.F))) Q
    rwa [ι_mix_pos hι rfl] at this

theorem int_off {v : HeightOneSpectrum (𝓞 D.host.F)} {a c : Formalism.IndefR.Lev.EAf D} (hv : v ∉ badPl ι a)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (phi D v : Formalism.IndefR.Lev.EAf D) * a + (1 - (phi D v : Formalism.IndefR.Lev.EAf D)) * c ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (int_iff hι _).2 fun Q => by
    by_cases h : Q.under (𝓞 D.host.F) = v
    · rw [ι_mix_pos hι h]
      by_contra hn
      exact hv ⟨Q, hn, h⟩
    · rw [ι_mix_neg hι h]
      exact (int_iff hι c).1 hc Q

end Local

section Level

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem red_cases {x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} (hS : x ∈ St β) (v : HeightOneSpectrum (𝓞 D.host.F))
    (PP : Pl D.host.E) : redFn β PP (piece (phi_idem' v) x) = redFn β PP x ∨ redFn β PP (piece (phi_idem' v) x) = 1 := by
  by_cases h : PP.under (𝓞 D.host.F) = v
  · exact Or.inl (redFn_piece (phi_idem v) _ hS PP (resS_phi_pos h))
  · exact Or.inr (redFn_piece_eq_one _ (piece_mem_St (phi_idem v) _ hS) PP (resS_phi_neg h))

theorem cmp_mem_of_mem (hH : L.P.H = ⊥) {g : GA D V} (hg : g ∈ levG V β L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    cmp V v g ∈ levG V β L := by
  have hx : finE V g ∈ lev D.sp.cm V.gram β L := hg.2
  have hS := parLev_St hx.1
  have hU := finE_mem_UA V (cmp V v g)
  refine ⟨cmp_mem_GfC V v g, ?_⟩
  show finE V (cmp V v g) ∈ lev D.sp.cm V.gram β L
  rw [finE_cmp] at hU ⊢
  have hSv := piece_mem_St (phi_idem v) (phi_idem' v) hS
  have h1 : rTup β L (finE V g) = 1 := by
    have := hx.2
    rw [hH] at this
    exact Subgroup.mem_bot.1 this
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hSv, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rcases red_cases hS v PP with e | e <;> rw [e]
    · exact parLev_g hx.1 hP
    · exact Subgroup.one_mem _
  · rcases red_cases hS v PP with e | e <;> rw [e]
    · exact parLev_q hx.1 hP
    · exact Subgroup.one_mem _
  · rw [hH]
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    show upperLeftBlock L.hr (redFn β PP.1 _) = 1
    rcases red_cases hS v PP.1 with e | e <;> rw [e]
    · exact congrFun h1 PP
    · exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_of_cmp_mem (hH : L.P.H = ⊥) {g : GA D V} (hf : g ∈ GfC V) (h : ∀ v, cmp V v g ∈ levG V β L) :
    g ∈ levG V β L := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E
  have hxv : ∀ v, piece (phi_idem' v) (finE V g) ∈ lev D.sp.cm V.gram β L := fun v => by
    have : finE V (cmp V v g) ∈ lev D.sp.cm V.gram β L := (h v).2
    rwa [finE_cmp] at this
  have hSt : ∀ v, piece (phi_idem' v) (finE V g) ∈ St β := fun v => parLev_St (hxv v).1
  have hS : finE V g ∈ St β := by
    refine mem_St_of_int (fun i j => ?_) (fun i j => ?_)
    · refine int_of_local hι _ ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j) fun v => ?_
      have := int_of_mem_St (hSt v) i j
      rw [piece_conj'] at this
      exact this
    · refine int_of_local hι _ ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j) fun v => ?_
      have := int_of_mem_St ((St β).inv_mem (hSt v)) i j
      rw [piece_inv', piece_conj'] at this
      exact this
  have hr : ∀ PP : Pl D.host.E, redFn β PP (finE V g) =
      redFn β PP (piece (phi_idem' (PP.under (𝓞 D.host.F))) (finE V g)) := fun PP =>
    (redFn_piece (phi_idem _) _ hS PP (resS_phi_pos rfl)).symm
  refine ⟨hf, mem_lev.2 ⟨mem_parLev.2 ⟨finE_mem_UA V g, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hr PP]
    exact parLev_g (hxv _).1 hP
  · rw [hr PP]
    exact parLev_q (hxv _).1 hP
  · rw [hH]
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    show upperLeftBlock L.hr (redFn β PP.1 _) = 1
    rw [hr PP.1]
    have h2 := (hxv (PP.1.under (𝓞 D.host.F))).2
    rw [hH] at h2
    exact congrFun (Subgroup.mem_bot.1 h2) PP

theorem finite_cmp (g : GA D V) : {v | cmp V v g ∉ levG V β L}.Finite := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E
  have hB : ((⋃ i, ⋃ j, badPl ι ((β⁻¹ * finE V g * β).1 i j)) ∪ (⋃ i, ⋃ j, badPl ι ((β⁻¹ * (finE V g)⁻¹ * β).1 i j)) ∪
      ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.under (𝓞 D.host.F)) '' ((L.Pg : Set _) ∪ (L.Q : Set _)))).Finite :=
    ((Set.finite_iUnion fun i => Set.finite_iUnion fun j => badPl_finite _).union
      (Set.finite_iUnion fun i => Set.finite_iUnion fun j => badPl_finite _)).union
      ((L.Pg.finite_toSet.union L.Q.finite_toSet).image _)
  refine hB.subset fun v hv => ?_
  by_contra hvB
  apply hv
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hvB
  obtain ⟨⟨a1, a2⟩, a3⟩ := hvB
  have hS : piece (phi_idem' v) (finE V g) ∈ St β := by
    refine mem_St_of_int (fun i j => ?_) (fun i j => ?_)
    · rw [piece_conj']
      exact int_off hι (a1 i j) (one_int i j)
    · rw [piece_inv', piece_conj']
      exact int_off hι (a2 i j) (one_int i j)
  have hU := finE_mem_UA V (cmp V v g)
  refine ⟨cmp_mem_GfC V v g, ?_⟩
  show finE V (cmp V v g) ∈ lev D.sp.cm V.gram β L
  rw [finE_cmp] at hU ⊢
  refine mem_lev_of_red _ _ β L _ hU hS fun PP hPP => ?_
  refine redFn_piece_eq_one _ hS PP (resS_phi_neg fun e => a3 ⟨PP, ?_, e⟩)
  exact hPP.imp (fun h => h) (fun h => h)

end Level

theorem levProd_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, LevProd R i := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  have hH : (R.datWp i R.triv).P.H = ⊥ := rfl
  refine ⟨fun k hk => hk.1, fun k _ => ?_, fun v => cmp (Wc D i) v, fun v f hf g => ?_, fun g hg =>
    ⟨⟨fun h v => cmp_mem_of_mem hH h v, mem_of_cmp_mem hH hg⟩, finite_cmp g⟩⟩
  · unfold levChi levFn
    have h1 : ∀ x, ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi x = 1 := by
      intro x
      unfold ext1
      split_ifs <;> rfl
    rw [h1, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul, Units.val_one]
    · intro PP hP
      exact absurd hP (Finset.notMem_empty _)
    · intro PP _
      exact Finset.prod_eq_one fun c hc => absurd hc (Finset.notMem_empty _)
  · obtain ⟨ε, hε, rfl⟩ := hf
    obtain rfl := placeIdem_unique hε (epsF_spec v)
    exact ⟨cmp_supp _ v g, cmp_triv _ v g⟩

end GlobalTheory.LevelProduct

end
