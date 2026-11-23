import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.TangentCombinationTransitivity
import Development.AutomorphicArithmetic.DivisorFrames.CutLatticeTwoEmbeddingsBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.height_charts_two_families :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X) (J : Type) (K : Charts Dw t V ρ' J) (W : Y.X.Opens) (p : ℕ) [Fact p.Prime] (n : ℕ), K.HTAt ρ W p n → ∀ (r s : ℕ) (f : (∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (f' : (∀ y : Y.X, Fin s → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (σ σ' : 𝓞 E →+* F), EigFr t p ρ f σ → EigFr t p ρ f' σ' → ∀ (M N : ℕ) (a : Fin M → Dw.La) (S S' : Fin N → Fin M → F) (κ : ℝ), CutAll Dw p σ a S κ → CutAll Dw p σ' a S' 0 → (∀ k : F →+* ℂ_[p], DualL Dw (k.comp σ') a (fun j m => k (S j m)) (fun j m => k (S' j m))) → 0 ≤ κ → κ + 2 ≤ n → ∀ (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn) (P : J → Matrix (Fin M) (Fin r) V.G.functionField) (P' : J → Matrix (Fin M) (Fin s) V.G.functionField), (∀ j, ChartCo t V ρ' (K.aff j) (K.e j) (fun m => K.h j (a m)) f T (P j)) → (∀ j, ChartCo t V ρ' (K.aff j) (K.e j) (fun m => K.h j (a m)) f' T' (P' j)) → Orth V W p K.U (fun j => constM V S * P j) T (fun j => constM V S' * P' j) T' := by
  intro E _ _ _ H Dw X t F _ _ Y V ρ' ρ J K W p hp n hK r s f f' σ σ' hf hf' M N a S S' κ hS hS' hD hκ hn T T' P P' hP hP'
    v e y z yt hT j hj u u' hu hu'
  have hv : (p : 𝓞 F) ∈ v.asIdeal := by
    have := residueCharacteristic_mem v
    rwa [hT.1] at this
  have hle : ∀ c, ‖ioOf p e c‖ ≤ 1 ↔ e.w c ≤ 1 := fun c => by rw [ioOf_le_one_iff p hv e, e.mem_O]
  have hlt : ∀ c, ‖ioOf p e c‖ < 1 → e.w c < 1 := fun c hc => by
    rcases eq_or_ne c 0 with rfl | h0
    · simp
    · have h1 := hle c⁻¹
      rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero _).2 h0)),
        inv_le_one₀ (e.w.pos h0)] at h1
      rw [← not_le, ← h1, not_le]
      exact hc
  obtain ⟨x, ch, hx, hch⟩ := hK v e y z yt hT
  obtain ⟨ex, hxx, b, hex, -, hPt, hE, hA⟩ := hch j hj
  obtain ⟨A, hA1, hA2⟩ := hA M r a f T (P j) (hP j)
  obtain ⟨A', hA1', hA2'⟩ := hA M s a f' T' (P' j) (hP' j)
  let k : F →+* ℂ_[p] := (ioOf p e).comp (algebraMap F (AlgebraicClosure F))
  obtain ⟨δ, hδ0, hδ, hc⟩ := hS k
  obtain ⟨δ', hδ0', hδ', hc'⟩ := hS' k
  have htan : ∀ i, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (spMap (dualMap (intO ℂ_[p]).subtype) ≫ ex i) :=
    fun i => GlobalTheory.LieMet.isTan_map _ rfl (hex.1 i)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hnd : ‖δ‖ = (p : ℝ) ^ (-κ) := by
    rw [← Real.exp_log (norm_pos_iff.2 hδ0), hδ, Real.rpow_def_of_pos hp0]
    congr 1; ring
  have hnd' : ‖δ'‖ = 1 := by
    rw [← Real.exp_log (norm_pos_iff.2 hδ0'), hδ']; simp
  have h1 : ‖δ‖ ≤ 1 := by
    rw [hnd]; exact Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
  have h2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ‖ := by
    rw [hnd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hp0]
    refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
    push_cast; linarith
  have hf0 := hf v e y
  have hf0' := hf' v e y
  rw [← hx] at hf0 hf0'
  have hI := (UpperTheory.tangent_combination_transitivity E H X t _ _ _ _ _ _ A htan hA1).2 hf0.1
  have hI' := (UpperTheory.tangent_combination_transitivity E H X t _ _ _ _ _ _ A' htan hA1').2 hf0'.1
  have key := UpperTheory.cut_lattice_two_embeddings_bound E H Dw p n _ _ b _ hPt (k.comp σ) (k.comp σ') M N r s a _ _ δ δ' A A' hc hc' (hD k) hδ0 h1 hnd'
    h2 hI hI' (fun i => hE _ _ (hA1 i) _ (hf0.2 i).2) (fun i => hE _ _ (hA1' i) _ (hf0'.2 i).2)
    (ioOf p e ∘ u) (ioOf p e ∘ u')
  have e1 := hA2 N S
  have e2 := hA2' N S'
  have m1 : ∀ i, (covMat (fun j m => k (S j m)) (fun m k => (hxx (a m) k : ℂ_[p])) A *ᵥ (ioOf p e ∘ u)) i =
      ioOf p e ((vals V (constM V S * P j) T z (below y.1) *ᵥ u) i) := fun i => by
    rw [RingHom.map_mulVec, e1]; rfl
  have m2 : ∀ i, (covMat (fun j m => k (S' j m)) (fun m k => (hxx (a m) k : ℂ_[p])) A' *ᵥ (ioOf p e ∘ u')) i =
      ioOf p e ((vals V (constM V S' * P' j) T' z (below y.1) *ᵥ u') i) := fun i => by
    rw [RingHom.map_mulVec, e2]; rfl
  have key2 := key (fun i => by rw [m1]; exact (hle _).2 (hu i)) (fun i => by rw [m2]; exact (hle _).2 (hu' i))
  refine hlt _ ?_
  rw [RingHom.map_dotProduct]
  rw [funext m1, funext m2] at key2
  exact key2
