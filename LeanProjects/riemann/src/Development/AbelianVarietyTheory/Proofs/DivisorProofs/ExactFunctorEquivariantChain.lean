import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

noncomputable section

namespace GlobalTheory.ChainGlue

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

theorem isAdd_of_epi {M N : AM B Λ} (f : M ⟶ N) [Epi f] (h : IsAdd M) : IsAdd N := fun a b => by
  have : Epi f.hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map f))
  have k : ∀ c, (M.ρ c : M.V ⟶ M.V) ≫ f.hom = f.hom ≫ (N.ρ c : N.V ⟶ N.V) := fun c => f.comm c
  rw [← cancel_epi f.hom, Preadditive.comp_add, ← k, ← k, ← k, h, Preadditive.add_comp]

theorem isAdd_mod (E : EPres B Λ) : IsAdd E.mod :=
  isAdd_of_epi (N := cokernel E.ψ) (cokernel.π E.ψ) E.add

theorem kills_of_iso {g : Γ(B.X, ⊤)} {F G : B.X.Modules} (e : F ≅ G) (h : Kills g G) : Kills g F := by
  unfold Kills at h ⊢
  rw [← cancel_mono e.hom, smulHom_comp, h, comp_zero, zero_comp]

theorem kills_mul {g : Γ(B.X, ⊤)} (c : Γ(B.X, ⊤)) {F : B.X.Modules} (h : Kills g F) : Kills (g * c) F := by
  unfold Kills at h ⊢
  rw [smulHom_mul, h, comp_zero]

variable (p : ℕ) [Fact p.Prime]

theorem isAdd_frobA (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {M : AM B Λ} (hM : IsAdd M) :
    IsAdd (frobA p h M) := fun a b => by
  haveI := Examples₂.additive_frobFun p h
  change (frobFun p h).map (M.ρ (a + b) : M.V ⟶ M.V) =
    (frobFun p h).map (M.ρ a : M.V ⟶ M.V) + (frobFun p h).map (M.ρ b : M.V ⟶ M.V)
  rw [hM, Functor.map_add]

theorem isFrob_of_iso (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {F G F' : B.X.Modules} (e : F ≅ G)
    (e' : F' ≅ (frobFun p h).obj G) : IsFrob p F F' :=
  ⟨h, ⟨e' ≪≫ (frobFun p h).mapIso e.symm⟩⟩

theorem dvd_of_root {γ : Γ(B.X, ⊤)} {n : ℕ} (h : IsRootOfP p γ (p ^ (n + 1))) {i : ℕ} (hi : i ≤ n + 1) :
    ∃ c : Γ(B.X, ⊤), γ ^ p ^ i * c = (p : Γ(B.X, ⊤)) := by
  obtain ⟨u, hu⟩ := h
  have h1 : γ ^ p ^ i ∣ γ ^ p ^ (n + 1) := pow_dvd_pow _ (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hi)
  have h2 : γ ^ p ^ (n + 1) ∣ (p : Γ(B.X, ⊤)) :=
    ⟨↑u⁻¹, by rw [hu, mul_comm (u : Γ(B.X, ⊤)), mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨c, hc⟩ := h1.trans h2
  exact ⟨c, hc.symm⟩

theorem locFree_iter (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {γ : Γ(B.X, ⊤)} {n : ℕ}
    (hγ : IsRootOfP p γ (p ^ (n + 1))) {F : B.X.Modules} (hF : LocFreeMod γ F) (i : ℕ) (hi : i ≤ n + 1) :
    LocFreeMod (γ ^ p ^ i) ((frobFun p h).obj^[i] F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih =>
    obtain ⟨c, hc⟩ := dvd_of_root p hγ hi
    rw [pow_succ, pow_mul] at hc
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    exact LocFreeQuot.of_isFrob p (ih (by omega)) hc (isFrob_of_iso p h (Iso.refl _) (Iso.refl _))

theorem part_iter (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {ι : Type} (φ : ι → ι) (P : ι → (AM B Λ ⥤ B.X.Modules))
    (hfrob : ∀ τ (M : AM B Λ), IsAdd M →
      Nonempty ((P (φ τ)).obj (frobA p h M) ≅ (frobFun p h).obj ((P τ).obj M)))
    {M : AM B Λ} (hM : IsAdd M) (τ : ι) (i : ℕ) : IsAdd ((frobA p h)^[i] M) ∧
      Nonempty ((P (φ^[i] τ)).obj ((frobA p h)^[i] M) ≅ (frobFun p h).obj^[i] ((P τ).obj M)) := by
  induction i with
  | zero => exact ⟨hM, ⟨Iso.refl _⟩⟩
  | succ i ih =>
    obtain ⟨h1, ⟨e⟩⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨e'⟩ := hfrob (φ^[i] τ) _ h1
    exact ⟨isAdd_frobA p h h1, ⟨e' ≪≫ (frobFun p h).mapIso e⟩⟩

theorem isExt_map (P : AM B Λ ⥤ B.X.Modules) [P.PreservesZeroMorphisms]
    (hex : ∀ (S : ShortComplex (AM B Λ)), S.ShortExact → IsAdd S.X₁ → IsAdd S.X₂ → IsAdd S.X₃ → (S.map P).ShortExact)
    {F₁ F₂ F₃ : AM B Λ} (h : IsExtA F₁ F₂ F₃) (a₁ : IsAdd F₁) (a₂ : IsAdd F₂) (a₃ : IsAdd F₃)
    {G₁ G₂ G₃ : B.X.Modules} (k₁ : Nonempty (P.obj F₁ ≅ G₁)) (k₂ : Nonempty (P.obj F₂ ≅ G₂))
    (k₃ : Nonempty (P.obj F₃ ≅ G₃)) : IsExt G₁ G₂ G₃ := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := h
  exact ⟨S.map P, hex S hS (isAdd_of_epi e₁.inv a₁) (isAdd_of_epi e₂.inv a₂) (isAdd_of_epi e₃.inv a₃),
    ⟨P.mapIso e₁ ≪≫ k₁.some⟩, ⟨P.mapIso e₂ ≪≫ k₂.some⟩, ⟨P.mapIso e₃ ≪≫ k₃.some⟩⟩

end SlopeTestRemainingChoices

theorem main : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {o : ℕ} (Q : EqChain p B Λ o) {ι : Type} (φ : ι → ι) (P : ι → (AM B Λ ⥤ B.X.Modules)) [∀ τ, (P τ).PreservesZeroMorphisms] (hlin : ∀ τ (M : AM B Λ) (g : Γ(B.X, ⊤)), IsAdd M → (P τ).map (smulA M g) = smulHom ((P τ).obj M) g) (hex : ∀ τ (S : ShortComplex (AM B Λ)), S.ShortExact → IsAdd S.X₁ → IsAdd S.X₂ → IsAdd S.X₃ → (S.map (P τ)).ShortExact) (hcok : ∀ τ {M N : AM B Λ} (f : M ⟶ N), IsAdd M → IsAdd N → Nonempty ((P τ).obj (cokernel f) ≅ cokernel ((P τ).map f))) (hvb : ∀ τ (E : EPres B Λ), ∃ r, GlobalTheory.VB.IsVB ((P τ).obj E.E) r ∧ GlobalTheory.VB.IsVB ((P τ).obj E.E') r ∧ IsIso (B.genRes.map ((P τ).map E.ψ))) (hfrob : ∀ τ (M : AM B Λ), IsAdd M → Nonempty ((P (φ τ)).obj (frobA p Q.hp M) ≅ (frobFun p Q.hp).obj ((P τ).obj M))) (hret : ∀ τ (M : AM B Λ), IsAdd M → ∃ (i : (P τ).obj M ⟶ M.V) (q : M.V ⟶ (P τ).obj M), i ≫ q = 𝟙 _) (hdiv : ∀ n < o, ∃ c : Γ(B.X, ⊤), Q.g = Q.γ n ^ p ^ n * c), ∃ Ch : Chain p B φ o, Ch.π = Q.π ∧ Ch.g = Q.g ∧ ∀ τ,
      (∃ r vb vb' iso, Ch.lw τ = ⟨r, (P τ).obj Q.lw.E, (P τ).obj Q.lw.E', vb, vb', (P τ).map Q.lw.ψ, iso⟩) ∧
      (∃ r vb vb' iso, Ch.oo τ = ⟨r, (P τ).obj Q.oo.E, (P τ).obj Q.oo.E', vb, vb', (P τ).map Q.oo.ψ, iso⟩) := by
  intro O _ _ _ p _ _ _ B Λ _ o Q ι φ P _ hlin hex hcok hvb hfrob hret hdiv
  choose r vb vb' iso using hvb
  let pt : ι → EPres B Λ → Pres B := fun τ E =>
    ⟨r τ E, (P τ).obj E.E, (P τ).obj E.E', vb τ E, vb' τ E, (P τ).map E.ψ, iso τ E⟩
  have hpt : ∀ τ E, Nonempty ((P τ).obj E.mod ≅ (pt τ E).mod) := fun τ E => hcok τ E.ψ E.add' E.add
  have hfree : ∀ n < o, ∀ i ≤ n + 1, ∀ τ,
      LocFreeMod (Q.γ n ^ p ^ i) ((frobFun p Q.hp).obj^[i] ((P τ).obj (Q.l n).mod)) := fun n hn i hi τ => by
    obtain ⟨a, b, hab⟩ := hret τ _ (isAdd_mod (Q.l n))
    exact locFree_iter p Q.hp (Q.γ_root n hn) (LocFreeQuot.of_retract (Q.l_free n hn) a b hab) i hi
  have hl : ∀ (n i : ℕ) (τ : ι), ∃ R : Pres B, n < o → i ≤ n + 1 →
      Nonempty (R.mod ≅ (frobFun p Q.hp).obj^[i] ((P τ).obj (Q.l n).mod)) := fun n i τ => by
    by_cases h : n < o ∧ i ≤ n + 1
    · obtain ⟨-, R, hR⟩ := (LocFreeQuot.main O p B _ _ (hfree n h.1 i h.2 τ)).1
        (dvd_of_root p (Q.γ_root n h.1) h.2)
      exact ⟨R, fun _ _ => hR⟩
    · exact ⟨pt τ (Q.l n), fun a b => (h ⟨a, b⟩).elim⟩
  choose l hl using hl
  refine ⟨{
      π := Q.π, g := Q.g, π_root := Q.π_root, g_root := Q.g_root,
      lw := fun τ => pt τ Q.lw, wl := fun τ => (P τ).map Q.wl,
      lw_wl := fun τ => ?_,
      oo := fun τ => pt τ Q.oo, q := fun n τ => pt τ (Q.q n), l := l,
      c3 := fun τ => isExt_map (P τ) (hex τ) Q.c3 (isAdd_of_epi (cokernel.π _) Q.lw.add') (isAdd_mod _) (isAdd_mod _)
        (hcok τ Q.wl Q.lw.add Q.lw.add') (hpt τ _) (hpt τ _),
      step := fun n hn τ => isExt_map (P τ) (hex τ) (Q.step n hn) (isAdd_mod _) (isAdd_mod _) (isAdd_mod _)
        (hpt τ _) (hpt τ _) ⟨(hl n 0 τ hn (by omega)).some.symm⟩,
      l_frob := fun n hn i hi τ => ?_,
      l_last := fun n hn τ => ?_,
      q_frob := fun n hn τ => ?_ }, rfl, rfl, fun τ => ⟨⟨_, _, _, _, rfl⟩, ⟨_, _, _, _, rfl⟩⟩⟩
  · change (P τ).map Q.lw.ψ ≫ (P τ).map Q.wl = smulHom ((P τ).obj Q.lw.E') Q.π
    rw [← Functor.map_comp, Q.lw_wl, hlin τ _ _ Q.lw.add']
  · obtain ⟨e⟩ := hl n i τ hn (by omega)
    obtain ⟨e'⟩ := hl n (i + 1) τ hn (by omega)
    rw [Function.iterate_succ_apply'] at e'
    refine ⟨kills_of_iso e ?_, isFrob_of_iso p Q.hp e e'⟩
    obtain ⟨c, hc⟩ := hdiv n hn
    obtain ⟨d, hd⟩ : Q.γ n ^ p ^ i ∣ Q.g :=
      (pow_dvd_pow _ (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hi)).trans ⟨c, hc⟩
    rw [hd]
    exact kills_mul d (LocFreeQuot.smulHom_eq_zero (hfree n hn i (by omega) τ))
  · obtain ⟨e⟩ := hl n (n + 1) τ hn le_rfl
    obtain ⟨-, ⟨e₁⟩⟩ := part_iter p Q.hp φ P hfrob (isAdd_mod (Q.l n)) τ (n + 1)
    obtain ⟨e₂⟩ := Q.l_last n hn
    obtain ⟨e₃⟩ := hcok (φ^[n + 1] τ) (smulA Q.lw.E' (p : Γ(B.X, ⊤))) Q.lw.add' Q.lw.add'
    exact ⟨e ≪≫ e₁.symm ≪≫ (P _).mapIso e₂ ≪≫ e₃ ≪≫ cokernelIsoOfEq (hlin _ _ _ Q.lw.add')⟩
  · obtain ⟨e⟩ := hpt τ (Q.q (n + 1))
    obtain ⟨e'⟩ := hpt (φ τ) (Q.q n)
    obtain ⟨e₁⟩ := Q.q_frob n hn
    obtain ⟨e₂⟩ := hfrob τ _ (isAdd_mod (Q.q (n + 1)))
    refine ⟨kills_of_iso e.symm ?_, isFrob_of_iso p Q.hp e.symm (e'.symm ≪≫ (P _).mapIso e₁ ≪≫ e₂)⟩
    have h0 : smulA (Q.q (n + 1)).mod Q.g = 0 := Action.Hom.ext (Q.q_kill n hn)
    unfold Kills
    rw [← hlin τ _ _ (isAdd_mod _), h0, Functor.map_zero]

end GlobalTheory.ChainGlue

end
