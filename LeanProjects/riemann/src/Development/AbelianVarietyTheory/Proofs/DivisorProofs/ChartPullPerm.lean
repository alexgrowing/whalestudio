import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjSwap

section Charts

variable {X Y Y' : Scheme.{0}}

def pullInv {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso B A) :
    LB.Iso A' B' where
  s p := (res (fun y hy => ⟨a.le _ hy.2, b.le _ hy.1⟩ :
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)))
    (pullU h _ (w.s (a.idx p.2, b.idx p.1))))⁻¹

theorem gm_pullInv {Z : Scheme.{0}} {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (b : ChartPull B' B h) (w : LB.Iso B A) (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullInv a b w).s p) =
      (gm (r ≫ h) z (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans
    (gm_pull r h z _ (show h (r z) ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) from ⟨a.le _ hz.2, b.le _ hz.1⟩) _)))

theorem pullInv_isGen {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    {w : LB.Iso B A} (hw : w.IsGen) : (pullInv a b w).IsGen := fun p q => unit_ext fun y hy => by
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((pullInv a b w).s p) =
        (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ := fun p hp =>
    (gm_pullInv a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) :=
    ⟨⟨a.le _ hy.1.2, b.le _ hy.1.1⟩, ⟨a.le _ hy.2.2, b.le _ hy.2.1⟩⟩
  have e := congrArg (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1))))
    (hw (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1))
  have e' : gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)) =
      gm h y (A.U (a.idx p.2) ⊓ A.U (a.idx q.2)) (A.g (a.idx p.2) (a.idx q.2)) *
        (gm h y (B.U (b.idx p.1) ⊓ B.U (b.idx q.1)) (B.g (b.idx p.1) (b.idx q.1)))⁻¹ *
        gm h y (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) (w.s (a.idx q.2, b.idx q.1)) :=
    (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B A h y (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1) hm) (gm_res h y _ hm _))))
  have d : gm (𝟙 Y') y ((LB.div B' A').U p ⊓ (LB.div B' A').U q) ((LB.div B' A').g p q) =
      gm (𝟙 Y') y (B'.U p.1 ⊓ B'.U q.1) (B'.g p.1 q.1) * (gm (𝟙 Y') y (A'.U p.2 ⊓ A'.U q.2) (A'.g p.2 q.2))⁻¹ :=
    gm_div A' B' (𝟙 Y') y p q hy
  refine (gm_res _ y _ hy _).trans ((val p hy.1).trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  rw [d, gm_res (𝟙 Y') y _ hy, val q hy.2, b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, e']
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem gm_gen_congr {M : LB X} (t : LB.Gen M) {r r' : Y ⟶ X} (hr : r = r') (y : Y) {i i' : M.ι} (hi : i = i') :
    gm r y (M.U i) (t.s i) = gm r' y (M.U i') (t.s i') := by
  subst hr hi; rfl

theorem gm_g_congr (L : LB X) (f : Y ⟶ X) (y : Y) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') :
    gm f y (L.U i ⊓ L.U j) (L.g i j) = gm f y (L.U i' ⊓ L.U j') (L.g i' j') := by
  subst hi hj; rfl

def chartPullPerm (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : K ≃ K) (hc : ∀ k, φ' k = h ≫ φ (e k)) (hε : ∀ k, ε (e k) = ε k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j k := j (e.symm k)
  le j y hy := Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy (e.symm k)
    rw [hc, Equiv.apply_symm_apply] at this
    exact this
  g y j j' hj hj' := by
    refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_ (gm_linComb L φ ε h y _ _
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj' (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)).symm)
    refine Fintype.prod_equiv e _ _ fun k => ?_
    simp only [hε, Category.id_comp, hc]
    exact congrArg (· ^ ε k) (gm_g_congr L _ y (congrArg j (e.symm_apply_apply k)).symm
      (congrArg j' (e.symm_apply_apply k)).symm)

end Charts

section Sums

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I = ∏ i ∈ I, x i := by
  have hnd : ((List.finRange n).filter (· ∈ I)).Nodup := (List.nodup_finRange n).filter _
  calc psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
        unfold psum
        generalize ((List.finRange n).filter (· ∈ I)) = l
        induction l with
        | nil => rfl
        | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]; rfl
    _ = ∏ i ∈ I, x i := by
        rw [← List.prod_toFinset x hnd]
        congr 1
        ext i
        simp

theorem psum_perm {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G))
    (π : Equiv.Perm (Fin n)) (hx : ∀ i, x' i = σ ≫ x (π i)) (I : Finset (Fin n)) :
    psum G x' I = σ ≫ psum G x (I.map π.toEmbedding) := by
  calc psum G x' I = ∏ i ∈ I, x' i := psum_eq_prod x' I
    _ = ∏ i ∈ I, σ ≫ x (π i) := by simp only [hx]
    _ = σ ≫ ∏ i ∈ I, x (π i) := (map_prod (preHom (G := G) σ) _ I).symm
    _ = σ ≫ ∏ i ∈ I.map π.toEmbedding, x i := by rw [Finset.prod_map]; rfl
    _ = σ ≫ psum G x (I.map π.toEmbedding) := by rw [psum_eq_prod]

end Sums

def swapIdx : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).finsetCongr.trans Equiv.ulift.symm)

theorem swapIdx_down (I : ULift.{0} (Finset (Fin 2))) :
    (swapIdx I).down = I.down.map (Equiv.swap (0 : Fin 2) 1).toEmbedding := rfl

end GlobalTheory.MumFam.AdjSwap

namespace GlobalTheory.MumFam

open AdjSwap in

theorem adj_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₁ a' a h' h := by
  intro R _ _ Q₁ Q₂ a a' h h' ⟨ha, ha', hc, hc', w, hw, hv⟩
  let σ : Q₂.B ⊗ Q₁.B ⟶ Q₁.B ⊗ Q₂.B := lift (snd Q₂.B Q₁.B) (fst Q₂.B Q₁.B)
  have hA : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] K.down).left =
      σ.left ≫ (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hB : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] K.down).left =
      σ.left ≫ (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hε : ∀ K : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - (swapIdx K).down.card)) = (-1) ^ (2 - K.down.card) :=
    fun K => by rw [swapIdx_down, Finset.card_map]
  let cA : ChartPull (cubeLB Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] Q₁.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L) σ.left :=
    chartPullPerm Q₁.M.L _ _ _ σ.left swapIdx hA hε
  let cB : ChartPull (cubeLB Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] Q₂.M.L)
      (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) σ.left :=
    chartPullPerm Q₂.M.L _ _ _ σ.left swapIdx hB hε
  refine ⟨ha', ha, hc', hc, pullInv cA cB w, pullInv_isGen cA cB hw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hp : (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left ≫ σ.left =
      (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left := by
    rw [← Over.comp_left]; congr 1; simp [σ]
  have key : adjVal (pullInv cA cB w) (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left z J₁ J₂ =
      (adjVal w (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left z J₂ J₁)⁻¹ := by
    let p' := (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left
    have m₁ := hJ₁.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left) p'
    have m₂ := hJ₂.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left) p'
    have e1 := gm_pullInv cA cB w p' z
      (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left),
        fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)) ⟨m₁, m₂⟩
    have i₁ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] k.down).left := fun k => by
      rw [hA, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have i₂ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] k.down).left := fun k => by
      rw [hB, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have e2 := gm_gen_congr w hp z (Prod.ext (funext fun k => congrArg J₂ (i₁ k)) (funext fun k => congrArg J₁ (i₂ k)) :
      ((cA.idx (fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)),
        cB.idx (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left))) :
          (LB.div (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L)
            (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)).ι) =
        (fun I => J₂ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] I.down).left),
          fun I => J₁ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left)))
    exact e1.trans (congrArg (·⁻¹) e2)
  have o := hv y' y z J₂ J₁ hJ₂ hJ₁
  rw [Q₂.tau_symm (h y') y z J₁ hJ₁, Q₁.tau_symm y' (h' y) z J₂ hJ₂] at o
  rw [key, o, inv_mul_cancel_left]

end GlobalTheory.MumFam
