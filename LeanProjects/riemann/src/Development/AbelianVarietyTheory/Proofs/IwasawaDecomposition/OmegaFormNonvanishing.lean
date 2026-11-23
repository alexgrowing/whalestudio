import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Lift

def sgnGL (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : GL (Fin n) S := Units.map (Int.castRingHom _).toMonoidHom ε

theorem sgnGL_val (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : (sgnGL n S ε).1 = (ε : ℤ) • 1 := (zsmul_one _).symm

theorem sgnGL_comm {n : ℕ} {S : Type} [CommRing S] (ε : ℤˣ) (x : GL (Fin n) S) : x * sgnGL n S ε = sgnGL n S ε * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, sgnGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem bc_sgnGL {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) :
    Formalism.UG.bc f (sgnGL n S ε) = sgnGL n S' ε :=
  Units.ext (map_intCast (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) S') (ε : ℤ))

theorem map_sgn {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) (i j : Fin n) :
    (sgnGL n S' ε).1 i j = f ((sgnGL n S ε).1 i j) := by
  rw [← bc_sgnGL f]; rfl

theorem frGL_sgn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (ε : ℤˣ) : frGL β (sgnGL n _ ε) = sgnGL n _ ε := by
  have h : intGL F E n (sgnGL n _ ε) = sgnGL n _ ε := bc_sgnGL (Formalism.L2.Herm.intAf F E).subtype ε
  rw [frGL, MonoidHom.comp_apply, h, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sgnGL_comm, mul_inv_cancel_right]

theorem exists_matrix_sign {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P x = sgnGL n _ ε) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - (sgnGL n _ ε).1) = M • N :=
  GlobalTheory.LevelUnique.exists_matrix_hat hfr T hJ hx ⟨sgnGL n _ ε, rfl⟩
    (fun P hP => by rw [h P hP, redFn_frGL, bc_sgnGL]) hb hK
    (fun i j => by
      rw [frGL_sgn]
      exact map_sgn (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom ε i j)

theorem eq_sgn_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : GL (Fin n) S} {ε : ℤˣ}
    (e : x.1.submatrix (Fin.castLE h) (Fin.castLE h) = (sgnGL r S ε).1) : x = sgnGL n S ε := by
  subst hr
  exact Units.ext e

theorem sign_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {ε : ℤˣ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (sgnGL n R ε).1 *ᵥ z = M • w₃) : x - (ε : ℤ) • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, sgnGL_val, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {D : D7}

theorem finVec_sub_zsmul (V : HSp D) (x y : Fin V.rank → D.host.E) (e : ℤ) :
    finVec V (x - e • y) = finVec V x - e • finVec V y := by
  funext j
  exact (map_sub (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) (x j) (e • y j)).trans
    (congrArg (fun t => finVec V x j - t) (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) e (y j)))

theorem hatV_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) : GlobalTheory.Ker.hatV Λ = Formalism.L2.Pj.latHat V := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  rw [hl]; rfl

theorem mulVec_mem {V : HSp D} {k : GA D V} (hk : GlobalTheory.Member.FinCong V 1 k) :
    ∀ z ∈ Formalism.L2.Pj.latHat V, (finHom V k).1 *ᵥ z ∈ Formalism.L2.Pj.latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [one_nsmul] at e
  rw [sub_eq_iff_eq_add.1 e]
  exact add_mem hy hz

theorem isMov_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) Λ Λ := by
  have hk' : Lev.finE V k⁻¹ ∈ St β := by rw [map_inv]; exact inv_mem hk
  have h1 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk)
  have h2 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk')
  intro u
  rw [hatV_eq hβ]
  change _ ↔ ∃ u₀ ∈ _, u = (finHom V k).1 *ᵥ u₀
  constructor
  · intro hu
    exact ⟨_, h2 u hu, by rw [← GlobalTheory.Member.LatMove.fin_mul, mul_inv_cancel, GlobalTheory.Member.LatMove.fin_one]⟩
  · rintro ⟨u₀, h0, rfl⟩
    exact h1 u₀ h0

theorem cong_on_half {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w) :
    ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      K *ᵥ finVec V (ι a) - K' *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  intro a ha
  refine Submodule.smul_induction_on ha (fun b hb a _ => ?_) ?_
  · obtain ⟨w, hw, e⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
    have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
      rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
    exact ⟨w, hw, by rw [e₀, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, e]⟩
  · rintro x y ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    have e₀ : finVec V (ι (x + y)) = finVec V (ι x) + finVec V (ι y) := by
      rw [map_add]; funext i; exact TensorProduct.tmul_add _ _ _
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [e₀, Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e, ← e']
    abel

theorem mark_calc {R : Type} [CommRing R] {n : ℕ} {Hm K K' : Matrix (Fin n) (Fin n) R} {m x z w₁ w₂ w₃ : Fin n → R} {M : ℕ}
    (e₁ : m - Hm *ᵥ x = M • w₁) (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - K' *ᵥ z = M • w₃) :
    m - Hm *ᵥ (K' *ᵥ z) = M • (w₁ + Hm *ᵥ (w₂ + w₃)) := by
  rw [smul_add, ← Matrix.mulVec_smul, smul_add, ← e₁, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.mulVec_sub, sub_add_sub_cancel]

theorem exists_cong_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = sgnGL _ _ ε) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (sgnGL V.rank (Af D.host.F ⊗[D.host.F] D.host.E) ε).1 *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_sign hfr T hJ hk ε h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (ε : ℤˣ) (hg : ∀ P, g P = sgnGL _ _ ε) :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = sgnGL _ _ ε := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := congrArg Units.val (e.trans (hg ⟨P, hP⟩))
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_sgn_of_submatrix hr L.hr e'

theorem exists_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a : La}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) (e : finVec V (ι a) = M • w) :
    ∃ b, a = M • b := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm a⟩ (h5 ▸ hw) e
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  refine ⟨c, hι.1 ?_⟩
  rw [map_nsmul]
  exact congrArg Subtype.val ev

theorem sign_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a a' : La} {e : ℤ}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1)
    (h : finVec V (ι a') - e • finVec V (ι a) = M • w) : ∃ b, a' = e • a + M • b := by
  obtain ⟨b, hb⟩ := exists_div (a := a' - e • a) hι hM hw (by rw [map_sub, map_zsmul, finVec_sub_zsmul, h])
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

theorem mu_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) {k : GA D W}
    {x : (AE D)ˣ} (hx : IsDetRoot W k x) : castDict hV mu k = ((χ x : Circle) : ℂ) := by
  subst hV
  exact h.2 k x hx

theorem mem_iff_prod_le {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) (P : Pl E) :
    P ∈ T ↔ ∏ Q ∈ T, Q.asIdeal ≤ P.asIdeal := by
  rw [P.isPrime.prod_le]
  refine ⟨fun h => ⟨P, h, le_rfl⟩, ?_⟩
  rintro ⟨Q, hQ, h⟩
  rwa [← HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)]

end GlobalTheory.OneMapRef.Lift
